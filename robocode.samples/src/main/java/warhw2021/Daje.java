package warhw2021;

import java.awt.*;
import java.awt.geom.Point2D;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import robocode.AdvancedRobot;
import robocode.BulletHitEvent;
import robocode.BulletMissedEvent;
import robocode.HitByBulletEvent;
import robocode.HitRobotEvent;
import robocode.HitWallEvent;
import robocode.RobotDeathEvent;
import robocode.Rules;
import robocode.ScannedRobotEvent;
import robocode.util.Utils;

// API help : https://robocode.sourceforge.io/docs/robocode/robocode/Robot.html

/**
 * Daje - a robot by Nicola Ferraro
 */
public class Daje extends AdvancedRobot {

    private static final boolean DEBUG = false;

    private static final int MIN_BORDER_DISTANCE = 110;
    private static final int ABSOLUTE_STEP = 5000;
    private static final int RAMMING_DEVIATION_MIN_ENEMIES = 7;
    private static final int RAMMING_DEVIATION_MIN = 10;
    private static final int RAMMING_DEVIATION_MAX = 45;
    private static final double RAMMING_ENERGY_RATIO_IMBALANCE = 2.70;
    private static final int FIRE_BEARING_DISTANCE = 3;
    private static final double ENEMY_SPEED_VARIATION = 0.15;
    private static final double WORST_ENEMY_TOLERANCE = 0.35;
    private static final double DEVIATION_FROM_CENTER_MAX = 10;
    private static final double DEVIATION_FROM_CENTER_MULTIPLIER = 3.0;
    private static final double BULLET_SAVING_PRECISION = 1.0;
    private static final double BULLET_SAVING_DISTANCE = 0.5;
    private static final double BULLET_MIN_ATTEMPTS_ENERGY = 5.0;
    private static final double BULLET_SAVE_SHOTS_WHEN_LOSING = 4.1;
    private static final int INITIALIZATION_MAX_TIME = 10;
    private static final double INITIALIZATION_MAX_DAMAGE = 2.9;
    private static final double INITIALIZATION_MAX_ENERGY_LOSS = 5.0;

    private int direction = ABSOLUTE_STEP;
    private Map<String, RobotProfile> profiles = new HashMap<String, RobotProfile>();
    private Double initialEnergy;
    private int velocityVariationDir = 1;

    public Daje() {
    }

    public void run() {

        setBodyColor(Color.RED);
        setGunColor(Color.YELLOW);
        setRadarColor(Color.YELLOW);
        setBulletColor(Color.YELLOW);
        setScanColor(Color.YELLOW);

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

    private double rammingDeviation(String targetRobot) {
        int enemies = Math.min(getOthers(), RAMMING_DEVIATION_MIN_ENEMIES);
        double numRatio = 1.0 - (enemies * 1.0 / RAMMING_DEVIATION_MIN_ENEMIES);

        double energyRatio = numRatio;
        RobotProfile p = getProfile(targetRobot);
        if (p != null && p.energy != null) {
            energyRatio = getEnergy() / (p.energy * RAMMING_ENERGY_RATIO_IMBALANCE);
            energyRatio = Math.min(1.0, energyRatio);
        }
        double ratio = Math.sqrt(numRatio * energyRatio);
        if (DEBUG) {
            out.println("Compute ramming: numRatio=" + numRatio + ", energyRatio=" + energyRatio + ", combined=" + ratio);
        }
        double ramming = RAMMING_DEVIATION_MIN + ratio * (RAMMING_DEVIATION_MAX - RAMMING_DEVIATION_MIN);
        return ramming;
    }

    private boolean isPersonalEnemy(String robotName) {
        RobotProfile targetProfile = getProfile(robotName);
        if (targetProfile.dead) {
            return false;
        }
        RobotProfile worstEnemy = null;
        for (RobotProfile p : this.profiles.values()) {
            if (p.dead) {
                continue;
            }
            if (worstEnemy == null || p.energyLoss > worstEnemy.energyLoss) {
                worstEnemy = p;
            }
        }
        boolean ok = worstEnemy == null || targetProfile.energyLoss >= worstEnemy.energyLoss * (1 - WORST_ENEMY_TOLERANCE);
        if (DEBUG && worstEnemy != null) {
            System.out.println("Worst enemy: " + worstEnemy.name + " (" + worstEnemy.energyLoss + "), current target: " + robotName + " (" + targetProfile.energyLoss + ") - targeting: " + ok);
        }
        return ok;
    }

    public void onScannedRobot(ScannedRobotEvent e) {
        if (e.isSentryRobot()) {
            return;
        }

        if (initialize(e)) {
            getProfile(e.getName()).energy = e.getEnergy();
            return;
        }
        
        if(!isPersonalEnemy(e.getName())) {
            getProfile(e.getName()).energy = e.getEnergy();
            return;
        }

        RobotProfile p = getProfile(e.getName());
        
        double bearingDegrees = getHeading() + e.getBearing();
        double bearingDegreesFromRadar = Utils.normalRelativeAngleDegrees(bearingDegrees - getRadarHeading());

        double hitPrecision = 1.0;
        if (p.attemptsEnergy >= BULLET_MIN_ATTEMPTS_ENERGY) {
            hitPrecision = p.hitsEnergy / p.attemptsEnergy;
        }
        double longDistance = Math.min(getBattleFieldHeight(), getBattleFieldWidth()) / 2;
        double approachingDistance = Math.min(getBattleFieldHeight(), getBattleFieldWidth()) / 3;
        double distance = e.getDistance();
        double distancePrecision = 1.0;
        if (distance > longDistance) {
            distancePrecision = 0;
        } else if (distance >= approachingDistance) {
            distancePrecision = 1.0 - (distance - approachingDistance) / (longDistance - approachingDistance);
        }
        distancePrecision = Math.min(1.0, distancePrecision);
        distancePrecision = Math.max(0.0, distancePrecision);

        double bulletPower = Rules.MAX_BULLET_POWER - (1.0 - hitPrecision) * BULLET_SAVING_PRECISION - (1.0 - distancePrecision) * BULLET_SAVING_DISTANCE;
        bulletPower = Math.min(Rules.MAX_BULLET_POWER, bulletPower);
        bulletPower = Math.max(Rules.MIN_BULLET_POWER, Math.min(e.getEnergy()/4, bulletPower));
        bulletPower = Math.min(getEnergy() / BULLET_SAVE_SHOTS_WHEN_LOSING, bulletPower); // Save some shots when we're dying
        
        if (DEBUG) {
            out.println("Bullet power: (" + bulletPower + ") hitPrecision=" + hitPrecision + ", distancePrecision=" + distancePrecision);
        }

        Double lastEnergy = p.energy;
        if (lastEnergy != null) {
            double diff = lastEnergy - e.getEnergy();
            if (p.goAwayStrategy && diff >= 0.1 && diff <= 3.0) {
                reverseDirection();
            }
        }
        getProfile(e.getName()).energy = e.getEnergy();
        
        double bulletSpeed = (20.0 - 3.0 * bulletPower);

        int maxIterations = 50;
        int iterations = 0;
        double time = 0.0;
        while ((++iterations) <= maxIterations) {
            Point enemyPos = getFuturePoint(e, time);
            if (Utils.isNear(time, 0.0)) {
                p.lastLocation = enemyPos;
            }
            double oldTime = time;
            time = Point2D.distance(getX(), getY(), enemyPos.getX(), enemyPos.getY()) / bulletSpeed;
            if (Utils.isNear(time, oldTime)) {
                break;
            }
        }

        Point predictedPoint = getFuturePoint(e, time);
        double predictedX = predictedPoint.getX();
        double predictedY = predictedPoint.getY();

        if (DEBUG) {
            System.out.println("Iterations=" + iterations + ", time=" + time + ", Predicted x=" + predictedX + ", y=" + predictedY);
        }

        double theta = Utils.normalAbsoluteAngle(Math.atan2(predictedX - getX(), predictedY - getY()));
        
        double absoluteBearing = getHeadingRadians() + e.getBearingRadians();
        setTurnRadarRightRadians(Utils.normalRelativeAngle(absoluteBearing - getRadarHeadingRadians()));
        double gunDiffRadians = Utils.normalRelativeAngle(theta - getGunHeadingRadians());
        setTurnGunRightRadians(gunDiffRadians);

        double approachDeviation = rammingDeviation(e.getName());
        if (DEBUG) {
            System.out.println("Ramming: " + approachDeviation);
        }

        if (this.direction > 0) {
            setTurnRight(Utils.normalRelativeAngleDegrees(deviate(e.getBearing() + 90 - approachDeviation)));
        } else {
            setTurnRight(Utils.normalRelativeAngleDegrees(deviate(e.getBearing() + 90 + approachDeviation)));
        }

        if (Math.toDegrees(gunDiffRadians) <= FIRE_BEARING_DISTANCE) { 
            if (getGunHeat() == 0 && getEnergy() >= bulletPower) {
                p.attemptsEnergy+=bulletPower;
                if (DEBUG) {
                    System.out.println("Fire against " + p.name + "(" + bulletPower + ")");
                }
                fire(bulletPower);
            }
        }

        if (bearingDegreesFromRadar == 0) {
            scan();
        }
    }

    private boolean initialize(ScannedRobotEvent e) {
        if (initialEnergy == null) {
            initialEnergy = getEnergy();
        }

        if (getTime() > INITIALIZATION_MAX_TIME) {
            return false;
        }

        if (getEnergy() <= initialEnergy - INITIALIZATION_MAX_ENERGY_LOSS) {
            return false;
        }

        double sumDamage = 0;
        for (RobotProfile p : this.profiles.values()) {
            sumDamage += p.energyLoss;
        }
        if (sumDamage > INITIALIZATION_MAX_DAMAGE) {
            return false;
        }

        if (DEBUG) {
            System.out.println("Initialization phase (" + getTime() + " / " + INITIALIZATION_MAX_TIME + ")...");
        }

        RobotProfile sp = getProfile(e.getName());
        Point l = getFuturePoint(e, 0.0);
        sp.lastLocation = l;

        List<Point> others = new ArrayList<>();
        for (RobotProfile p : this.profiles.values()) {
            if (p.dead || p.lastLocation == null) {
                continue;
            }
            others.add(p.lastLocation);
        }
        if (others.size() == 0) {
            others.add(new Point(getX(), getY()));
        }

        double sumx=0, sumy=0;
        for (Point loc : others) {
            sumx += loc.x;
            sumy += loc.y;
        }
        Point center = new Point(sumx / others.size(), sumy / others.size());

        double escapex, escapey;
        if (center.x < getBattleFieldWidth() / 2) {
            escapex = center.x + getBattleFieldWidth()/2;
        } else {
            escapex = center.x - getBattleFieldWidth()/2;
        }
        if (center.y < getBattleFieldHeight() / 2) {
            escapey = center.y + getBattleFieldHeight()/2;
        } else {
            escapey = center.y - getBattleFieldHeight()/2;
        }
        
        escapex = Math.min(Math.max(MIN_BORDER_DISTANCE, escapex), getBattleFieldWidth() - MIN_BORDER_DISTANCE);
        escapey = Math.min(Math.max(MIN_BORDER_DISTANCE, escapey), getBattleFieldHeight() - MIN_BORDER_DISTANCE);
        
        double bearing = getBearingDegrees(escapex, escapey);
        setTurnRight(bearing);
        setTurnRadarRight(360);
        if (DEBUG) {
            double distance = Math.sqrt(Math.pow(getX() - escapex, 2) + Math.pow(getY() - escapey, 2));
            System.out.println("Escape location x=" + escapex + ", y=" + escapey + ", distance=" + distance);
        }

        // Set closest target as next
        RobotProfile nextTarget = null;
        double nextTargetDistance = Double.MAX_VALUE;
        for (RobotProfile p : this.profiles.values()) {
            p.energyLoss = 0; // reset
            if (p.lastLocation == null) {
                continue;
            }
            double d = Math.sqrt(Math.pow(getX() - p.lastLocation.x, 2) + Math.pow(getY() - p.lastLocation.y, 2));
            if (d < nextTargetDistance) {
                nextTargetDistance = d;
                nextTarget = p;
            }
        }
        if (nextTarget != null) {
            nextTarget.energyLoss=1.0;
        }

        return true;
    }


    private Point getFuturePoint(ScannedRobotEvent e, double time) {
        double absoluteBearing = getHeadingRadians() + e.getBearingRadians();
        double enemyX = getX() + e.getDistance() * Math.sin(absoluteBearing);
        double enemyY = getY() + e.getDistance() * Math.cos(absoluteBearing);

        double velocityCorrector = 1 + (this.velocityVariationDir * ENEMY_SPEED_VARIATION);
        double velocity = e.getVelocity() * velocityCorrector;

        double predictedX = enemyX + Math.sin(e.getHeadingRadians()) * velocity * time;
        double predictedY = enemyY + Math.cos(e.getHeadingRadians()) * velocity * time;

        if (predictedX < 18.0
            || predictedY < 18.0
            || predictedX > getBattleFieldWidth() - 18.0
            || predictedY > getBattleFieldHeight() - 18.0) {
            predictedX = Math.min(Math.max(18.0, predictedX),
                                    getBattleFieldWidth() - 18.0);
            predictedY = Math.min(Math.max(18.0, predictedY),
                                    getBattleFieldHeight() - 18.0);
        }

        return new Point(predictedX, predictedY);
    }

    private double deviate(double bearing) {
        double minDistance = 15;
        if (Math.abs(getX() - getBattleFieldWidth()/2) <= minDistance && Math.abs(getY() - getBattleFieldHeight()/2) <= minDistance) {
            // Keep the bearing when close to the center
            return bearing;
        }

        double maxDeviationDegrees = Math.min(DEVIATION_FROM_CENTER_MAX, getOthers() * DEVIATION_FROM_CENTER_MULTIPLIER);

        double centerBearing = getBearingDegrees(getBattleFieldWidth() / 2, getBattleFieldHeight() / 2);
        
        double bearingDiff = bearing - centerBearing;

        double modified = bearing;
        if (bearingDiff >=0 && bearingDiff <= maxDeviationDegrees) {
            modified = centerBearing + maxDeviationDegrees; 
        } else if (bearingDiff <=0 && bearingDiff >= -maxDeviationDegrees){
            modified = centerBearing - maxDeviationDegrees;
        }
        if (DEBUG && Math.abs(modified - bearing) >= 0.1) {
            System.out.println("Deviation original=" + bearing + ", modified=" + modified + ", num=" + getOthers() + ", max=" + maxDeviationDegrees + ", current=" + (modified - bearing));
        }
        return modified;
    }
    
    double getBearingDegrees(double x, double y) {
        double b = Math.PI/2 - Math.atan2(y - this.getY(), x - this.getX());
        double brad = Utils.normalRelativeAngle(b - this.getHeadingRadians());
        return Utils.normalRelativeAngleDegrees(brad / Math.PI * 180);
    }


    @Override
    public void onHitByBullet(HitByBulletEvent e) {
        RobotProfile p = getProfile(e.getName());
        p.energyLoss+=e.getPower();
        p.goAwayStrategy = !p.goAwayStrategy;
    }

    @Override
    public void onRobotDeath(RobotDeathEvent e) {
        RobotProfile p = getProfile(e.getName());
        p.dead = true;
    }

    @Override
    public void onBulletHit(BulletHitEvent event) {
        getProfile(event.getName()).hitsEnergy+=event.getBullet().getPower();
    }

    @Override
    public void onBulletMissed(BulletMissedEvent event) {
        this.velocityVariationDir = - this.velocityVariationDir;
    }
    

    /**
     * onHitRobot:  Back up!
     */
    public void onHitRobot(HitRobotEvent e) {
        RobotProfile p = getProfile(e.getName());
        p.energyLoss+=0.6;
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
            profile = new RobotProfile(name);
            this.profiles.put(name, profile);
        }
        return profile;
    }

    private static class RobotProfile {
        private String name;
        private Double energy;
        private boolean goAwayStrategy = true;
        private double energyLoss;
        private boolean dead;
        private double attemptsEnergy;
        private double hitsEnergy;
        private Point lastLocation;
        
        private RobotProfile(String name) {
            this.name = name;
        }
    }

    

    private static class Point {
        private double x,y;
        Point(double x, double y) {
            this.x = x;
            this.y = y;
        }
        public double getX() {
            return x;
        }
        public double getY() {
            return y;
        }
    }
}
