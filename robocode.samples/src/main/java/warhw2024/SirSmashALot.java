package warhw2024;

import java.awt.*;

import robocode.AdvancedRobot;
import robocode.HitByBulletEvent;
import robocode.HitRobotEvent;
import robocode.HitWallEvent;
import robocode.ScannedRobotEvent;
import robocode.TurnCompleteCondition;

public class SirSmashALot extends AdvancedRobot {

    private int direction = 500;

    @Override
    public void run() {
        setBodyColor(Color.DARK_GRAY);
        setGunColor(Color.BLUE);
        setRadarColor(Color.LIGHT_GRAY);
        setBulletColor(Color.RED);
        setScanColor(Color.LIGHT_GRAY);

        int move = 1;
        while (true) {
            setAhead(direction);
            if (move == 2) {
                turnGunRight(360);
            } else if (move < 5) {
                setTurnLeft(30);
                turnGunLeft(90);
                waitFor(new TurnCompleteCondition(this));
            } else if (move == 8) {
                turnGunLeft(360);
            } else {
                setTurnRight(30);
                turnGunRight(90);
                waitFor(new TurnCompleteCondition(this));
            }

            if (move > 9) {
                move = 1;
            } else {
                move++;
            }
        }
    }

    @Override
    public void onHitRobot(HitRobotEvent e) {
        if (e.isMyFault()) {
            if (canFire() && e.getBearing() > -10 && e.getBearing() < 10) {
                fire(3);
            }

            reverseDirection();
        }
    }

    @Override
    public void onHitByBullet(HitByBulletEvent event) {
        System.out.println("Ouch!!!");
    }

    @Override
    public void onHitWall(HitWallEvent e) {
        // Bounce off!
        reverseDirection();
    }

    @Override
    public void onScannedRobot(ScannedRobotEvent e) {
        if (!canFire()) {
            return;
        }

        if (e.getDistance() < 80 && getEnergy() > 16) {
            fire(3);
        } else if (e.getEnergy() > 10) {
            setFire(2);
        } else if (e.getEnergy() > 4) {
            setFire(1);
        } else if (e.getEnergy() > 2) {
            setFire(.5);
        } else if (e.getEnergy() > .4) {
            setFire(.1);
        }
    }

    private boolean canFire() {
        return getGunHeat() == 0;
    }

    private void reverseDirection() {
        direction = -direction;
        setAhead(direction);
    }
}
