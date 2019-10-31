package fusewarhw2019;

import java.awt.*;
import java.awt.geom.Point2D;
import java.util.HashMap;
import java.util.Map;

import robocode.AdvancedRobot;
import robocode.HitByBulletEvent;
import robocode.HitRobotEvent;
import robocode.HitWallEvent;
import robocode.Rules;
import robocode.ScannedRobotEvent;
import robocode.util.Utils;

// API help : https://robocode.sourceforge.io/docs/robocode/robocode/Robot.html

/**
 * HelloWorld - a robot by (your name here)
 */
public class HelloWorld extends AdvancedRobot {

    private static final int MIN_BORDER_DISTANCE = 110;
    private static final int ABSOLUTE_STEP = 5000;
    private static final int APPROACH_DEVIATION = 12;
    private static final int FIRE_BEARING_DISTANCE = 3;

    private int direction = ABSOLUTE_STEP;
    private Map<String, RobotProfile> profiles = new HashMap<String, RobotProfile>();

    public HelloWorld() {
    }

    public void run() {

        setBodyColor(Color.BLACK);
        setGunColor(Color.RED);
        setRadarColor(Color.BLACK);
        setBulletColor(Color.BLACK);
        setScanColor(Color.BLACK);

        setAdjustRadarForRobotTurn(true);
        setAdjustGunForRobotTurn(true);
        setAdjustRadarForGunTurn(true);

        boolean farFromBorder = farFromBorder();

        setAhead(direction);
        setTurnRadarRight(360);

        while (true) {
            boolean nowFarFromBorder = farFromBorder();
            if (!nowFarFromBorder && farFromBorder) {
                reverseDirection();
            }
            farFromBorder = nowFarFromBorder;

            if (getRadarTurnRemaining() == 0.0) {
                setTurnRadarRight(360);
            }

            execute();
        }
    }

    /**
     * onHitWall:  There is a small chance the robot will still hit a wall
     */
    public void onHitWall(HitWallEvent e) {
        // Bounce off!
        reverseDirection();
    }

    public void reverseDirection() {
        this.direction = -direction;
        setAhead(this.direction);
    }

    public void onScannedRobot(ScannedRobotEvent e) {
        if (e.isSentryRobot()) {
            return;
        }
        double bearingDegrees = getHeading() + e.getBearing();
        double bearingDegreesFromGun = Utils.normalRelativeAngleDegrees(bearingDegrees - getGunHeading());
        double bearingDegreesFromRadar = Utils.normalRelativeAngleDegrees(bearingDegrees - getRadarHeading());

        double bulletPower = Math.min(4.5 - Math.abs(bearingDegreesFromGun) / 2 - e.getDistance() / 250, getEnergy() - Rules.MIN_BULLET_POWER);
        double myX = getX();
        double myY = getY();
        double absoluteBearing = getHeadingRadians() + e.getBearingRadians();
        double enemyX = getX() + e.getDistance() * Math.sin(absoluteBearing);
        double enemyY = getY() + e.getDistance() * Math.cos(absoluteBearing);
        double enemyHeading = e.getHeadingRadians();
        double enemyVelocity = e.getVelocity();

        RobotProfile p = getProfile(e.getName());
        Double lastEnergy = p.energy;
        if (lastEnergy != null) {
            double diff = lastEnergy - e.getEnergy();
            if (p.goAwayStrategy && diff >= 0.1 && diff <= 3.0) {
                reverseDirection();
            }
        }
        getProfile(e.getName()).energy = e.getEnergy();

        double deltaTime = 0;
        double battleFieldHeight = getBattleFieldHeight(),
            battleFieldWidth = getBattleFieldWidth();
        double predictedX = enemyX, predictedY = enemyY;

        while ((++deltaTime) * (20.0 - 3.0 * bulletPower) <
               Point2D.Double.distance(myX, myY, predictedX, predictedY)) {
            predictedX += Math.sin(enemyHeading) * enemyVelocity;
            predictedY += Math.cos(enemyHeading) * enemyVelocity;
            if (predictedX < 18.0
                || predictedY < 18.0
                || predictedX > battleFieldWidth - 18.0
                || predictedY > battleFieldHeight - 18.0) {
                predictedX = Math.min(Math.max(18.0, predictedX),
                                      battleFieldWidth - 18.0);
                predictedY = Math.min(Math.max(18.0, predictedY),
                                      battleFieldHeight - 18.0);
                break;
            }
        }

        double theta = Utils.normalAbsoluteAngle(Math.atan2(
            predictedX - getX(), predictedY - getY()));

        setTurnRadarRightRadians(Utils.normalRelativeAngle(absoluteBearing - getRadarHeadingRadians()));
        setTurnGunRightRadians(Utils.normalRelativeAngle(theta - getGunHeadingRadians()));

        if (this.direction > 0) {
            setTurnRight(Utils.normalRelativeAngleDegrees(e.getBearing() + 90 - APPROACH_DEVIATION));
        } else {
            setTurnRight(Utils.normalRelativeAngleDegrees(e.getBearing() + 90 + APPROACH_DEVIATION));
        }

        if (Math.abs(bearingDegreesFromRadar) <= FIRE_BEARING_DISTANCE) {
            if (getGunHeat() == 0 && getEnergy() > .2) {
                fire(bulletPower);
            }
        }

        if (bearingDegreesFromRadar == 0) {
            scan();
        }
    }

    @Override
    public void onHitByBullet(HitByBulletEvent e) {
        RobotProfile p = getProfile(e.getName());
        p.goAwayStrategy = !p.goAwayStrategy;
    }

    /**
     * onHitRobot:  Back up!
     */
    public void onHitRobot(HitRobotEvent e) {
        // If we're moving the other robot, reverse!
        if (e.isMyFault()) {
            reverseDirection();
        }
    }

    private boolean farFromBorder() {
        return getX() > MIN_BORDER_DISTANCE &&
               getY() > MIN_BORDER_DISTANCE &&
               getBattleFieldWidth() - getX() > MIN_BORDER_DISTANCE &&
               getBattleFieldHeight() - getY() > MIN_BORDER_DISTANCE;
    }

    private RobotProfile getProfile(String name) {
        RobotProfile profile = this.profiles.get(name);
        if (profile == null) {
            profile = new RobotProfile();
            this.profiles.put(name, profile);
        }
        return profile;
    }

    private static class RobotProfile {
        private Double energy;
        private boolean goAwayStrategy = true;
    }
}
