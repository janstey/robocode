package fusewarhw2019.elmeth;

import robocode.AdvancedRobot;
import robocode.HitRobotEvent;
import robocode.HitWallEvent;
import robocode.Robot;
import robocode.ScannedRobotEvent;

public abstract class Core {

    protected AdvancedRobot robot;
    private int weight;

    public Core(AdvancedRobot robot, int weight) {
        this.robot = robot;
        this.weight = weight;
    }

    @Override
    public String toString() {
        return String.format("%s: %s", getClass().getSimpleName(), weight);
    }

    public int getWeight() {
        return weight;
    }

    public void init() {
    }

    public abstract void run();

    public void onHitRobot(HitRobotEvent e) {
    }

    public void onScannedRobot(ScannedRobotEvent e) {
    }

    public void onHitWall(HitWallEvent e) {
    }

}
