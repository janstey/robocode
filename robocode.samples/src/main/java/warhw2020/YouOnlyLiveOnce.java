package warhw2020;

import java.awt.Color;
import java.awt.geom.Point2D;
import robocode.AdvancedRobot;
import robocode.HitByBulletEvent;
import robocode.HitRobotEvent;
import robocode.HitWallEvent;
import robocode.RobotDeathEvent;
import robocode.Rules;
import robocode.ScannedRobotEvent;


public class YouOnlyLiveOnce extends AdvancedRobot {

    //Const
    private double battleFieldHeight;
    private double battleFieldWidth;

    //Movement
    private double firePower = 3.0;
    private int i = 0;
    private int l = 0;
    private int j = 0;
    private boolean customMove = false;
    private String target = null;

    private double[] randomTurn = new double[] {
        Math.PI / 3 * Math.random(), 2 * Math.PI * Math.random(), Math.PI * Math.random(), Math.PI / 2 * Math.random(),
        Math.PI * Math.random(), Math.PI / 2 * Math.random(), Math.PI / 3 * Math.random(), Math.PI * Math.random(),
        Math.PI * Math.random(), 2 * Math.PI * Math.random(), Math.PI / 2 * Math.random(), 2 * Math.PI * Math.random(),
        Math.PI * Math.random(), 2 * Math.PI * Math.random(), Math.PI / 3 * Math.random(), 2 * Math.PI * Math.random()
    };

    private double[] randomDistances = new double[] {
        getRandomDistance(), getRandomDistance(), getRandomDistance(),
        getRandomDistance(), getRandomDistance(), getRandomDistance(),
        getRandomDistance(), getRandomDistance(), getRandomDistance(),
        getRandomDistance(), getRandomDistance(), getRandomDistance(),
        getRandomDistance(), getRandomDistance(), getRandomDistance(),
        getRandomDistance(), getRandomDistance(), getRandomDistance(),
        getRandomDistance(), getRandomDistance(), getRandomDistance(),
        getRandomDistance(), getRandomDistance(), getRandomDistance(),
        getRandomDistance(), getRandomDistance(), getRandomDistance(),
        getRandomDistance(), getRandomDistance(), getRandomDistance(),
        getRandomDistance(), getRandomDistance(), getRandomDistance(),
        getRandomDistance(), getRandomDistance(), getRandomDistance(),
        getRandomDistance(), getRandomDistance(), getRandomDistance(),
        getRandomDistance(), getRandomDistance(), getRandomDistance()
    };

    private double[] randomSpeed = new double[] {
        getRandomSpeed(), getRandomSpeed(), getRandomSpeed(), getRandomSpeed(),
        getRandomSpeed(), getRandomSpeed(), getRandomSpeed(), getRandomSpeed(),
        getRandomSpeed(), getRandomSpeed(), getRandomSpeed(), getRandomSpeed(),
        getRandomSpeed(), getRandomSpeed(), getRandomSpeed(), getRandomSpeed(),
        getRandomSpeed(), getRandomSpeed(), getRandomSpeed(), getRandomSpeed(),
        getRandomSpeed(), getRandomSpeed(), getRandomSpeed(), getRandomSpeed(),
        getRandomSpeed(), getRandomSpeed(), getRandomSpeed(), getRandomSpeed(),
        getRandomSpeed(), getRandomSpeed(), getRandomSpeed(), getRandomSpeed()
    };

    private double getRandomSpeed() {
        return Rules.MAX_VELOCITY * Math.random() / 2 + 2;
    }

    private double getRandomDistance() {
        return Math.random() * 100 + 0.1;
    }

    private final int maxi = randomTurn.length;
    private final int maxl = randomDistances.length;
    private final int maxj = randomSpeed.length;
    private double average_distance;
    private int last_time_seen = 0;

    public void run() {
        battleFieldHeight = this.getBattleFieldHeight();
        battleFieldWidth = this.getBattleFieldWidth();
        average_distance = (battleFieldHeight + battleFieldWidth) / 10;

        this.setBodyColor(Color.PINK);
        this.setGunColor(Color.MAGENTA);
        this.setRadarColor(Color.ORANGE);
        this.setScanColor(Color.LIGHT_GRAY);

        this.setAdjustRadarForGunTurn(false);
        this.setAdjustGunForRobotTurn(false);

        this.setTurnRadarLeft(360);

        execute();

        while (true) {
            if (this.getDistanceRemaining () < 10) {
//                double x = this.getX();
//                double y = this.getY();
//                if (x < average_distance) {
//                    this.setTurnRight(90 - this.getHeading());
//                } else if (x > battleFieldWidth - average_distance) {
//                    this.setTurnRight(-90 - this.getHeading());
//                } else if (y < average_distance) {
//                    this.setTurnRight(0 - this.getHeading());
//                } else if (y > battleFieldHeight - average_distance) {
//                    this.setTurnRight(180 - this.getHeading());
//                } else {
//                    this.setTurnRightRadians(randomTurn[i++]);
//                }
//
//                this.setMaxVelocity(randomSpeed[j++]);
//                this.setAhead(randomDistances[l++]);
                this.setTurnRadarLeft(360);

//                if (i >= maxi) {
//                    i = 0;
//                }
//                if (j >= maxj) {
//                    j = 0;
//                }
//                if (l >= maxl) {
//                    l = 0;
//                }
            }
            last_time_seen++;
            execute();
        }
    }


    public void onScannedRobot(ScannedRobotEvent e) {
        if (this.target == null
                && (e.getDistance() < 200
                || this.getOthers() < 2)) {
            System.out.println("Targeting "  + e.getName());
            this.target = e.getName();
        } else if (last_time_seen > 40
                && !e.getName().equals(this.target)){
            this.target = e.getName();
            System.out.println("Change target: "  + e.getName());
        }else if (!e.getName().equals(this.target)){
//            System.out.println("Not targeting " + e.getName());
            return;
        }

        last_time_seen = 0;

        if(e.getDistance() < 20 && this.getEnergy() > 30) {
            firePower = Rules.MAX_BULLET_POWER;
        }
        double degrees = inferFuturePosition(e) - this.getHeading();
        if(degrees > 180) {
            degrees = 360 - degrees;
        }
        this.turnRight(degrees);
        this.setMaxVelocity(Rules.MAX_VELOCITY);
        this.setAhead(e.getDistance());

        if (this.getGunHeat() == 0 && this.getEnergy() > 10) {
            //fire!!!!
            this.setFire(firePower);
        }
        execute();

        //are we low on energy?
        //we have to recover!
        if (this.getEnergy() > 80) {
            firePower = Rules.MAX_BULLET_POWER;
        } else if (this.getEnergy() > 60) {
            firePower = 2.0;
        } else if (this.getEnergy() > 40) {
            firePower = 1.5;
        } else {
            firePower = 0.5;
        }
    }

    public void onHitRobot(HitRobotEvent e) {
        if (this.target == null) {
            System.out.println("Targeting "  + e.getName());
            this.target = e.getName();
        } else if (last_time_seen > 40
                       && !e.getName().equals(this.target)){
            this.target = e.getName();
            System.out.println("Change target: "  + e.getName());
        }else if (!e.getName().equals(this.target)){
//            System.out.println("Not targeting " + e.getName());
            return;
        }

        last_time_seen = 0;
        if (e.isMyFault()) {
            this.setBack(20);
        }

        //Scan it to target and fire
        this.setTurnRadarLeft(this.getRadarHeading() - this.getHeading());
        execute();
    }

    public void onHitWall(HitWallEvent event) {
        //Run the other way around
        if (this.getX() < average_distance) {
            this.turnRight(90 - this.getHeading());
        } else if (this.getX() > battleFieldWidth - average_distance) {
            this.turnRight(-90 - this.getHeading());
        } else if (this.getY() < average_distance) {
            this.turnRight(0 - this.getHeading());
        } else {
            this.turnRight(180 - this.getHeading());
        }

        this.setMaxVelocity(Rules.MAX_VELOCITY);
        this.ahead(average_distance);
    }

    @Override
    public void onRobotDeath(RobotDeathEvent robot) {
        if(robot.getName().equals(this.target)) {
            this.target = null;
        }
    }

    private double inferFuturePosition(ScannedRobotEvent e) {
        //We need direction and how much distance:
        double bulletSpeed = 20 - firePower * Rules.MAX_BULLET_POWER;
        double time = e.getDistance() / bulletSpeed;

        //Current position
        double angle = this.getHeadingRadians() + e.getBearingRadians();
        double x = (this.getX() + Math.sin(angle) * e.getDistance());
        double y = (this.getY() + Math.cos(angle) * e.getDistance());

        //Position when bullet arrives
        x += Math.sin(Math.toRadians(e.getHeading())) * e.getVelocity() * time;
        y += Math.cos(Math.toRadians(e.getHeading())) * e.getVelocity() * time;

        //Position to angle
        return angleBetweenTwoPoints(getX(), getY(), x, y);
    }

    private double angleBetweenTwoPoints(double x1, double y1, double x2, double y2) {
        double xo = x2 - x1;
        double yo = y2 - y1;
        double d = Point2D.distance(x1, y1, x2, y2);
        double asin = Math.toDegrees(Math.asin(xo / d));
        double bearing = 0;

        if (xo > 0 && yo > 0) {
            bearing = asin;
        } else if (xo < 0 && yo > 0) {
            bearing = 360 + asin;
        } else if (xo > 0 && yo < 0) {
            bearing = 180 - asin;
        } else if (xo < 0 && yo < 0) {
            bearing = 180 - asin;
        }

        return bearing;
    }
}
