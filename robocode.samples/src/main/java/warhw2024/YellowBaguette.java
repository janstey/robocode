package warhw2024;

import robocode.*;

import java.awt.*;

public class YellowBaguette extends AdvancedRobot {

    private int distance = 200;
    private double turn = 8D;

    @Override
    public void run() {

        this.setColors(Color.YELLOW, Color.WHITE, Color.YELLOW);

        while (true) {
            doTheMove();
            doTheMove();
            doTheMove();
            doTheMove();
        }
    }



    @Override
    public void onHitRobot(HitRobotEvent e) {
        if (getGunHeat() == 0 && e.getBearing() > -10 && e.getBearing() < 10) {
            fire(3);
        }

    }

    @Override
    public void onHitWall(HitWallEvent e) {
        double nextTurn = turn + 30D;
        if (turn >= 180D ) {
            turn = turn -180D;
        } else {
            turn = nextTurn;
        }
        doTheMove();
    }

    @Override
    public void onScannedRobot(ScannedRobotEvent e) {
        if (e.getDistance() < 250 && getGunHeat() == 0) {
            fire(3);
        }
    }


    private void doTheMove(){
        setAhead(distance);
        setTurnRight(turn);
        setTurnGunRight(turn);
        waitFor(new TurnCompleteCondition(this));
    }

}
