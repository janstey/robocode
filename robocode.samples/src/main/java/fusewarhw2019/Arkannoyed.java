package fusewarhw2019;

import robocode.*;

import java.awt.Color;

public class Arkannoyed extends Robot {

    private boolean reverse = false;
    private boolean run = true;
    private boolean scan = true;
    private boolean scanningVerse = true;
    private int scanArc = 45;
    private int speed=150;
    private double WALL_DISTANCE = 36;

    public void run() {
        setColors(Color.white, Color.black, Color.white); // body,gun,radar
        setAdjustGunForRobotTurn(true);
        setAdjustRadarForGunTurn(true);
        WALL_DISTANCE = getWidth()*1.5;

        while (true) {
            keepGoing(speed);
            if (scan) {
                keepScanning(scanArc);
            }
        }
    }


    private void keepScanning(double pixels) {
        alignRadarIfBesideWalls();
        if (scanningVerse) {
            turnRadarRight(pixels);
        } else {
            turnRadarLeft(pixels);
        }
    }

    private void alignRadarIfBesideWalls() {
        if (run && ((north() && (getRadarHeading()<=90 || getRadarHeading()>=270))
            || (south() && (getRadarHeading()>=90 && getRadarHeading()<=270))
            || (east() && getRadarHeading()<=180)
                || (west() && getRadarHeading()>=180))
        ){
            scanningVerse = !scanningVerse;
        }
    }

    private boolean south() {
        return getY() <= WALL_DISTANCE;
    }

    private boolean north() {
        return getBattleFieldHeight() - getY() <= WALL_DISTANCE;
    }

    private boolean east() {
        return getBattleFieldWidth() - getX() <= WALL_DISTANCE;
    }

    private boolean west() {
        return getX() <= WALL_DISTANCE;
    }

    private void keepGoing(int pixels) {
        if (run) {
            if (!reverse) {
                ahead(pixels);
            } else {
                back(pixels);
            }
        }
    }

    /**
     * onScannedRobot: What to do when you see another robot
     */
    public void onScannedRobot(ScannedRobotEvent e) {
            alignGunToTarget(e.getBearing());
            fire(firePower(e));
            keepGoing(20);
            keepScanning(5);
    }

    private void alignGunToTarget(double bearing) {
        double arc = this.getHeading() - this.getGunHeading() + bearing;
        if (arc != 0) {
            turnGunAbs(arc);
            turnRadarAbs(this.getGunHeading() - this.getRadarHeading());
        }
    }

    private double firePower(ScannedRobotEvent e) {
        if (e.getDistance() < 100 || e.getBearing()%90==0) {
            setBulletColor(Color.red);
            return 2;
        } else if (e.getDistance() > 300 ) {
            setBulletColor(Color.green);
            return 0.5;
        } else {
            setBulletColor(Color.blue);
            return 1;
        }
    }

    /**
     * onHitByBullet: What to do when you're hit by a bullet
     */
    public void onHitByBullet(HitByBulletEvent e) {
        alignGunToTarget(e.getBearing());
        fire(0.5);
        if(!run || north() || south() || east() || west()) {
            speed = 50;
            if (e.getBearing()%90==0){
                goForIt(e.getBearing());
            }
        } else {
            speed = 150;
            reverse = !reverse;
            runAwayFrom(e.getBearing());
        }
    }

    private void goForIt(double bearing) {
        run = true;
        reverse = false;
        turnGunAbs(getGunHeading()-bearing);
        fire(3);
        turnRadarAbs(getRadarHeading()-bearing);
        turnHeadAbs(getHeading()-bearing);
        keepGoing(100);
    }

    private void runAwayFrom(double bearing) {
        turnHeadAbs(90 - bearing);
        keepGoing(100);
        turnHeadAbs(45 + bearing);
        keepGoing(100);
    }

    private void spin() {
        ahead(500);
        turnRight(500);
    }

    public void onHitRobot(HitRobotEvent e) {
        alignGunToTarget(e.getBearing());
        fire(3);
        if(!run){
            fire(2);
        } else {
            runAwayFrom(e.getBearing());
        }
    }

    /**
     * onHitWall: What to do when you hit a wall
     */
    public void onHitWall(HitWallEvent e) {
        if (e.getBearing() == 0) {
            stop();
            run = false;
        } else {
            back(10);
            stop();
            double arc = 90 - e.getBearing();
            turnHeadAbs(arc);
            run = true;
        }
        reverse = !reverse;
        revertRadar();
    }

    private void revertRadar() {
        double arc = (run ? 270 : 160) + this.getHeading() - this.getGunHeading();
        turnGunAbs(arc);
        turnRadarAbs(this.getGunHeading() - this.getRadarHeading());
    }

    private void turnHeadAbs(double arc){
        double arcAbs = Math.abs(arc);
        boolean negative = arc<0;
        if(!negative) {
            if (arcAbs > 180) {
                turnRight(360 - arcAbs);
            } else {
                turnLeft(arcAbs);
            }
        }else{
            if (arcAbs > 180) {
                turnLeft(360 - arcAbs);
            } else {
                turnRight(arcAbs);
            }
        }
    }

    private void turnGunAbs(double arc) {
        double arcAbs = Math.abs(arc);
        boolean negative = arc<0;
        if(!negative) {
            if (arcAbs > 180) {
                turnGunLeft(360 - arcAbs);
            } else {
                turnGunRight(arcAbs);
            }
        }else{
            if (arcAbs > 180) {
                turnGunRight(360 - arcAbs);
            } else {
                turnGunLeft(arcAbs);
            }
        }
    }

    private void turnRadarAbs(double arc) {
        double arcAbs = Math.abs(arc);
        boolean negative = arc<0;
        if(!negative) {
            if (arcAbs > 180) {
                turnRadarLeft(360 - arcAbs);
            } else {
                turnRadarRight(arcAbs);
            }
        }else{
            if (arcAbs > 180) {
                turnRadarRight(360 - arcAbs);
            } else {
                turnRadarLeft(arcAbs);
            }
        }
    }

}
