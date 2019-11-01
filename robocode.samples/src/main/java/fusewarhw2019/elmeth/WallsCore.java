package fusewarhw2019.elmeth;

import robocode.AdvancedRobot;
import robocode.HitRobotEvent;
import robocode.ScannedRobotEvent;

public class WallsCore extends Core {

    private boolean peek; // Don't turn if there's a robot there
    private double moveAmount; // How much to move

    public WallsCore(AdvancedRobot robot, int weight) {
        super(robot, weight);
    }

    @Override
    public void init() {
        // Initialize moveAmount to the maximum possible for this battlefield.
        moveAmount = Math.max(robot.getBattleFieldWidth(), robot.getBattleFieldHeight());
        // Initialize peek to false
        peek = false;

        // turnLeft to face a wall.
        // getHeading() % 90 means the remainder of
        // getHeading() divided by 90.
        robot.turnLeft(robot.getHeading() % 90);
        robot.ahead(moveAmount);
        // Turn the gun to turn right 90 degrees.
        peek = true;
        robot.turnGunRight(90);
        robot.turnRight(90);
    }

    @Override
    public void run() {
        // Look before we turn when ahead() completes.
        peek = true;
        // Move up the wall
        robot.ahead(moveAmount);
        // Don't look now
        peek = false;
        // Turn to the next wall
        robot.turnRight(90);
    }

    @Override
    public void onHitRobot(HitRobotEvent e) {
        // If he's in front of us, set back up a bit.
        if (e.getBearing() > -90 && e.getBearing() < 90) {
            robot.back(100);
        } // else he's in back of us, so set ahead a bit.
        else {
            robot.ahead(100);
        }
    }

    @Override
    public void onScannedRobot(ScannedRobotEvent e) {
        robot.fire(2);
        // Note that scan is called automatically when the robot is moving.
        // By calling it manually here, we make sure we generate another scan event if there's a robot on the next
        // wall, so that we do not start moving up it until it's gone.
        if (peek) {
            robot.scan();
        }
    }
}
