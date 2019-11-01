package fusewarhw2019.elmeth;

import robocode.AdvancedRobot;
import robocode.HitRobotEvent;
import robocode.Robot;
import robocode.ScannedRobotEvent;

public class SpinCore extends Core {

    public SpinCore(AdvancedRobot robot, int weight) {
        super(robot, weight);
    }

    @Override
    public void run() {
        // Tell the game that when we take move,
        // we'll also want to turn right... a lot.
        robot.setTurnRight(10000);
        // Limit our speed to 5
        robot.setMaxVelocity(5);
        // Start moving (and turning)
        robot.ahead(10000);
        // Repeat.

    }

    @Override
    public void onHitRobot(HitRobotEvent e) {
        if (e.getBearing() > -10 && e.getBearing() < 10) {
            robot.fire(3);
        }
        if (e.isMyFault()) {
            robot.turnRight(10);
        }
    }

    @Override
    public void onScannedRobot(ScannedRobotEvent e) {
        robot.fire(3);
    }
}
