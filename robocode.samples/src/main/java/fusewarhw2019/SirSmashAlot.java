package fusewarhw2019;

import java.awt.*;

import robocode.AdvancedRobot;
import robocode.HitByBulletEvent;
import robocode.HitRobotEvent;
import robocode.HitWallEvent;
import robocode.ScannedRobotEvent;
import robocode.TurnCompleteCondition;

/**
 * @author Christoph Deppisch
 */
public class SirSmashAlot extends AdvancedRobot {

    private boolean forward;

    @Override
    public void run() {
        setBodyColor(Color.DARK_GRAY);
        setGunColor(Color.RED);
        setRadarColor(Color.LIGHT_GRAY);
        setBulletColor(Color.RED);
        setScanColor(Color.LIGHT_GRAY);

        while (true) {
            setAhead(500);
            forward = true;
            setTurnRight(90);
            waitFor(new TurnCompleteCondition(this));
            setTurnLeft(180);
            waitFor(new TurnCompleteCondition(this));
            setTurnRight(180);
            waitFor(new TurnCompleteCondition(this));
        }
    }

    @Override
    public void onHitRobot(HitRobotEvent e) {
        if (canFire() && e.getBearing() > -10 && e.getBearing() < 10) {
            fire(3);
        }

        if (e.isMyFault()) {
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
        if (canFire()) {
            if (e.getDistance() < 50 && getEnergy() > 50) {
                fire(3);
                if (canFire()) {
                    fire(1);
                }
            } else {
                fire(1);
                if (canFire()) {
                    fire(1);
                }
            }
        }
    }

    private boolean canFire() {
        return getGunHeat() == 0;
    }

    private void reverseDirection() {
        if (forward) {
            setBack(500);
            forward = false;
        } else {
            setAhead(500);
            forward = true;
        }
    }
}
