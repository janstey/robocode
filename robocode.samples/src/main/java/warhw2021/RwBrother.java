package warhw2021;

import java.awt.Color;
import java.awt.Graphics2D;
import java.awt.geom.Line2D;

import robocode.AdvancedRobot;
import robocode.HitByBulletEvent;
import robocode.HitWallEvent;
import robocode.RobotDeathEvent;
import robocode.Rules;
import robocode.ScannedRobotEvent;
import robocode.util.Utils;

/**
 * Rwbrother - a robot by Alex
 * 
 * TODOs:
 * 
 * OnScannedRobotEvent, it might be possible to get the velocity.
 * This velocity may help to anticipate the next position of the enemy/targets.
 *
 */
public class RwBrother extends AdvancedRobot {
    private static final double DEGREE_TO_RAD = 0.0174533;
    
    // The 1000x1000 will be updated when init is called
    private static double AREA_WIDTH = 1000.0;
    private static double AREA_HEIGHT = 1000.0;

    Target enemy = new Target();

    /**
     * run: Rwbrother's default behavior
     */
    public void run() {
        init();

        // Robot main loop
        while (true) {
            move();
            gun();
            radar();
            execute();
        }
    }

    private void move() {
        if (getDistanceRemaining() > 0 || getTurnRemaining() > 0) {
            return;
        }
//      System.out.println("getX(): "+getX()+"/"+AREA_WIDTH);
//      System.out.println("getY(): "+getY()+"/"+AREA_HEIGHT);
        // 1 Radian = 57.2958 degree
        double dx = AREA_WIDTH / 2.0 - getX();
        double dy = AREA_HEIGHT / 2.0 - getY();

//      System.out.println("dx "+dx);
//      System.out.println("dy "+dy);
        double angleToTarget = Math.atan2(dx, dy);
//      System.out.println("angleToTarget "+angleToTarget + " ("+ angleToTarget * 57.2958 +"°)");
//      System.out.println("getHeadingRadians() "+getHeadingRadians()+ " ("+ getHeadingRadians() * 57.2958 +"°)");
        double targetAngle = Utils.normalRelativeAngle(angleToTarget - getHeadingRadians());
//      System.out.println("targetAngle "+targetAngle+ " ("+ targetAngle * 57.2958 +"°)");
        //double d = Math.sqrt(dx * dx + dy * dy);

//      System.out.println("Target Angle "+targetAngle);
        double impulse = AREA_HEIGHT / 4.0;
        if (targetAngle < -Math.PI / 2.0 || targetAngle > Math.PI / 2.0) {
            setAhead(-impulse);
//              System.out.println("Going back ("+-impulse+")");
        } else {
            setAhead(impulse);
//              System.out.println("Going ahead ("+impulse+")");
        }

        setTurnLeft(-90);
    }

    private void gun() {
        if (getGunTurnRemaining() > 0 || !enemy.acquired()) {
            return;
        }

        // Forget about the current target
        if (System.currentTimeMillis() - enemy.timestamp > 500) {
            enemy.forget();
        }

        // getHeading() - getGunHeading() + e.getBearing()
        double bearingRadians = enemybearingRadians + getHeadingRadians() - getGunHeadingRadians();
//      System.out.println("enemy.bearingRadians*57.2958 = "+enemy.bearingRadians*57.2958+" degrees against "+enemy.name);
//      System.out.println("bearingRadians = "+bearingRadians*57.2958+" degrees against "+enemy.name);

        if (bearingRadians < -Math.PI) {
            bearingRadians += Math.PI + Math.PI;
        } else if (bearingRadians > Math.PI) {
            bearingRadians -= Math.PI + Math.PI;
        }

        if (bearingRadians > 0) {
            setTurnGunRightRadians(bearingRadians);
//              System.out.println("setTurnGunRightRadians("+bearingRadians+")");
        } else {
            setTurnGunLeftRadians(-bearingRadians);
//              System.out.println("setTurnGunLeftRadians("+-bearingRadians+")");
        }

        if (Math.abs(bearingRadians) < 0.1 && enemy.distance < AREA_WIDTH) {
            // We don't need to turn the gun that much, we may have a target
            double power = 0.1 + (2.9 * (1 - (enemy.distance / (AREA_WIDTH))));
            fire(power);
        }
    }

    private void radar() {
//      double radarTurn = getHeadingRadians() + enemy.bearingRadians - getRadarHeadingRadians();
//      setTurnRadarRightRadians(Utils.normalRelativeAngle(radarTurn));
        scan();
        if (getRadarTurnRemaining() == 0.0)
            setTurnRadarRightRadians(Double.POSITIVE_INFINITY);

        // Absolute angle towards target
        double angleToEnemy = getHeadingRadians() + enemy.bearingRadians;

        // Subtract current radar heading to get the turn required to face the
        // enemy, be sure it is normalized
        double radarTurn = Utils.normalRelativeAngle(angleToEnemy - getRadarHeadingRadians());

        // Distance we want to scan from middle of enemy to either side
        // The 36.0 is how many units from the center of the enemy robot it
        // scans.
        double extraTurn = Math.min(Math.atan(36.0 / enemy.distance), Rules.RADAR_TURN_RATE_RADIANS);

        // Adjust the radar turn so it goes that much further in the direction
        // it is going to turn
        // Basically if we were going to turn it left, turn it even more left,
        // if right, turn more right.
        // This allows us to overshoot our enemy so that we get a good sweep
        // that will not slip.
        if (radarTurn < 0)
            radarTurn -= extraTurn;
        else
            radarTurn += extraTurn;

        // Turn the radar
        setTurnRadarRightRadians(radarTurn);
    }

    private void init() {
        AREA_WIDTH = getBattleFieldWidth();
        AREA_HEIGHT = getBattleFieldHeight();

        setColors(Color.blue, Color.white, Color.red);

//    setTurnRadarRight(Double.POSITIVE_INFINITY);
    }

// Interesting tips:
// Rules.MAX_BULLET_POWER and Rules.MIN_BULLET_POWER.
// When one of your bullets hits an enemy, you collect back 3 * bullet power
// You can use the getOthers() method to know how many live enemies are in the battlefield.
// To save between battles you will have to save to a file.
// degree, 0 is up. clockwise

    /**
     * onScannedRobot: What to do when you see another robot
     */
    static class Target {
        String name;
        double x;
        double y;
        double distance;
        double bearingRadians;
        long timestamp;

        void tryLock(ScannedRobotEvent e) {
            String currentName = e.getName();
            if (currentName.equals(name)) {
                // update information on locked target
//                      x = e.getX();
//                      y = e.getY();
                distance = e.getDistance();
                bearingRadians = e.getBearingRadians();
                timestamp = System.currentTimeMillis();
//                      System.out.println("Update target distance: "+distance);
//                      System.out.println("Update target bearingRadians: "+bearingRadians);
            } else {
                double currentDistance = e.getDistance();
                if (name == null || currentDistance < distance) {
                    System.out.println("Acquiring a new target " + currentName);
                    name = currentName;
                    tryLock(e);
                }
            }
        }

        void forget() {
            name = null;
            System.out.println("Forgetting current target");
        }

        boolean acquired() {
            return name != null;
        }
    }

    public void onScannedRobot(ScannedRobotEvent e) {
        /*
         * double distance = e.getDistance(); if(distance < AREA_WIDTH/2){
         * double power=0.1+(2.9*(1-(distance/(ARE1A_WIDTH/2)))); fire(power); }
         */
        enemy.tryLock(e);
    }

    public void onRobotDeath(RobotDeathEvent e) {
        if (e.getName().equals(enemy.name)) {
//              System.out.println("Target "+enemy.name+" died, no more locking this target");
            enemy.forget();
        }
    }

    public void onPaint(Graphics2D g) {
        if (enemy != null && enemy.acquired()) {

            double angle = getHeadingRadians() + enemy.bearingRadians;
            if (angle < -Math.PI) {
                angle += Math.PI + Math.PI;
            } else if (angle > Math.PI) {
                angle -= Math.PI + Math.PI;
            }
            Line2D.Double line = new Line2D.Double(getX(), getY(), getX() + enemy.distance * Math.sin(angle), getY() + enemy.distance * Math.cos(angle));
//              double distance;
//              double bearingRadians;
            g.setColor(java.awt.Color.RED);
            g.draw(line);
        }
    }

    /**
     * onHitByBullet: What to do when you're hit by a bullet
     */
    public void onHitByBullet(HitByBulletEvent e) {
    }

    /**
     * onHitWall: What to do when you hit a wall
     */
    public void onHitWall(HitWallEvent e) {
    }
}
