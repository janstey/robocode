package warhw2024;

import robocode.*;
import robocode.util.Utils;

import java.awt.geom.Point2D;
import java.util.HashMap;
import java.util.Map;

/**
 * TheDodgingPony - a robot by (valder)
 */
public class TheDodgingPony extends AdvancedRobot {
    private static final int MIN_BORDER_DISTANCE = 110;
    private static final int ABSOLUTE_STEP = 5000;
    private static final int RAMMING_DEVIATION_MIN_ENEMIES = 2;
    private static final int RAMMING_DEVIATION_MIN = 10;
    private static final int RAMMING_DEVIATION_MAX = 45;
    private static final double RAMMING_ENERGY_RATIO_IMBALANCE = 2.70;
    private static final int FIRE_BEARING_DISTANCE = 3;
    private static final double ENEMY_SPEED_VARIATION = 0.15;
    private static final double DEVIATION_FROM_CENTER_MAX = 10;
    private static final double DEVIATION_FROM_CENTER_MULTIPLIER = 3.0;
    private static final double BULLET_SAVING_DISTANCE = 0.5;
    private static final double BULLET_SAVE_SHOTS_WHEN_LOSING = 4.1;

    private int movementDirection = 1;
    private int velocityVariationDir = 1;

    private Map<String, Double> enemyEnergyLevels = new HashMap<String, Double>();

    public void run() {
        boolean farFromBorder = farFromBorder();

        setAhead(movementDirection);
        setTurnRadarRight(360);

        while (true) {
            boolean nowFarFromBorder = farFromBorder();
            if (!nowFarFromBorder && farFromBorder) {
                reverseDirection();
                setAhead(ABSOLUTE_STEP * movementDirection);
            }
            farFromBorder = nowFarFromBorder;

            if (getRadarTurnRemaining() == 0.0) {
                setTurnRadarRight(360);
            }

            execute();
        }
    }

    public void onScannedRobot(ScannedRobotEvent e) {
        if (e.isSentryRobot()) {
            return;
        }

        Double previousEnemyEnergy = this.enemyEnergyLevels.get(e.getName());
        if (previousEnemyEnergy == null) {
            // init enemy energy as we have seen it for the first time
            previousEnemyEnergy = e.getEnergy();
            this.enemyEnergyLevels.put(e.getName(), previousEnemyEnergy);
        }

        // Try to stay perpendicular to the opponent
        setTurnRight(e.getBearing() + 90 - 30 * movementDirection);

        // If the bot has a "small" energy drop probably it fired
        double changeInEnergy = previousEnemyEnergy - e.getEnergy();
        if (changeInEnergy > 0 && changeInEnergy <= 3) {
            // Try to dodge!
            reverseDirection();
            setAhead((e.getDistance() / 4 + 25) * movementDirection);
        }

        // Track the new energy level
        this.enemyEnergyLevels.put(e.getName(), e.getEnergy());

        // aiming and firing
        double bearingDegrees = getHeading() + e.getBearing();
        double bearingDegreesFromRadar = Utils.normalRelativeAngleDegrees(bearingDegrees - getRadarHeading());

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

        double bulletPower = Rules.MAX_BULLET_POWER - (1.0 - distancePrecision) * BULLET_SAVING_DISTANCE;
        bulletPower = Math.min(Rules.MAX_BULLET_POWER, bulletPower);
        bulletPower = Math.max(Rules.MIN_BULLET_POWER, Math.min(e.getEnergy()/4, bulletPower));
        bulletPower = Math.min(getEnergy() / BULLET_SAVE_SHOTS_WHEN_LOSING, bulletPower);

        double bulletSpeed = (20.0 - 3.0 * bulletPower);

        int maxIterations = 50;
        int iterations = 0;
        double time = 0.0;
        while ((++iterations) <= maxIterations) {
            Coordinate enemyPos = getFuturePoint(e, time);
            double oldTime = time;
            time = Point2D.distance(getX(), getY(), enemyPos.getX(), enemyPos.getY()) / bulletSpeed;
            if (Utils.isNear(time, oldTime)) {
                break;
            }
        }

        Coordinate predictedPoint = getFuturePoint(e, time);
        double predictedX = predictedPoint.getX();
        double predictedY = predictedPoint.getY();

        double theta = Utils.normalAbsoluteAngle(Math.atan2(predictedX - getX(), predictedY - getY()));

        double absoluteBearing = getHeadingRadians() + e.getBearingRadians();
        setTurnRadarRightRadians(Utils.normalRelativeAngle(absoluteBearing - getRadarHeadingRadians()));
        double gunDiffRadians = Utils.normalRelativeAngle(theta - getGunHeadingRadians());
        setTurnGunRightRadians(gunDiffRadians);

        double approachDeviation = rammingDeviation(e.getName());

        if (this.movementDirection > 0) {
            setTurnRight(Utils.normalRelativeAngleDegrees(deviate(e.getBearing() + 90 - approachDeviation)));
        } else {
            setTurnRight(Utils.normalRelativeAngleDegrees(deviate(e.getBearing() + 90 + approachDeviation)));
        }

        if (Math.toDegrees(gunDiffRadians) <= FIRE_BEARING_DISTANCE) {
            if (getGunHeat() == 0 && getEnergy() >= bulletPower) {
                fire(bulletPower);
            }
        }

        if (bearingDegreesFromRadar == 0) {
            scan();
        }
    }

    public void onHitByBullet(HitByBulletEvent e) {
        // Try to stay perpendicular to the direction of being it
        turnRight(e.getBearing() + 90 - 30 * movementDirection);
        // and move
        reverseDirection();
        setAhead((60) * movementDirection);
    }

    public void onHitWall(HitWallEvent e) {
        // Bounce off!
        reverseDirection();
    }

    public void onHitRobot(HitRobotEvent e) {
        // If we're moving towards the other robot, reverse!
        if (e.isMyFault()) {
            reverseDirection();
        }
    }

    public void onBulletMissed(BulletMissedEvent event) {
        this.velocityVariationDir = - this.velocityVariationDir;
    }

    public void reverseDirection() {
        this.movementDirection = -movementDirection;
    }

    private boolean farFromBorder() {
        return getX() > MIN_BORDER_DISTANCE &&
                getY() > MIN_BORDER_DISTANCE &&
                getBattleFieldWidth() - getX() > MIN_BORDER_DISTANCE &&
                getBattleFieldHeight() - getY() > MIN_BORDER_DISTANCE;
    }

    private Coordinate getFuturePoint(ScannedRobotEvent e, double time) {
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

        return new Coordinate(predictedX, predictedY);
    }

    private double deviate(double bearing) {
        double minDistance = 15;
        if (Math.abs(getX() - getBattleFieldWidth()/2) <= minDistance && Math.abs(getY() - getBattleFieldHeight()/2) <= minDistance) {
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

        return modified;
    }

    private double rammingDeviation(String targetRobot) {
        int enemies = Math.min(getOthers(), RAMMING_DEVIATION_MIN_ENEMIES);
        double numRatio = 1.0 - (enemies * 1.0 / RAMMING_DEVIATION_MIN_ENEMIES);

        double energyRatio = numRatio;
        Double lastTrackedEnergy = enemyEnergyLevels.get(targetRobot);
        if (lastTrackedEnergy != null) {
            energyRatio = getEnergy() / (lastTrackedEnergy * RAMMING_ENERGY_RATIO_IMBALANCE);
            energyRatio = Math.min(1.0, energyRatio);
        }
        double ratio = Math.sqrt(numRatio * energyRatio);

        double ramming = RAMMING_DEVIATION_MIN + ratio * (RAMMING_DEVIATION_MAX - RAMMING_DEVIATION_MIN);
        return ramming;
    }

    double getBearingDegrees(double x, double y) {
        double b = Math.PI/2 - Math.atan2(y - this.getY(), x - this.getX());
        double brad = Utils.normalRelativeAngle(b - this.getHeadingRadians());
        return Utils.normalRelativeAngleDegrees(brad / Math.PI * 180);
    }

    private static class Coordinate {
        private double x,y;
        Coordinate(double x, double y) {
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