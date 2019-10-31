package fusewarhw2019;

import java.awt.Color;

import robocode.AdvancedRobot;
import robocode.BulletHitBulletEvent;
import robocode.BulletHitEvent;
import robocode.DeathEvent;
import robocode.HitByBulletEvent;
import robocode.HitRobotEvent;
import robocode.HitWallEvent;
import robocode.ScannedRobotEvent;

public class Scratsh extends AdvancedRobot {
	
	private boolean scannedRobot;

	@Override
	public void run() {
		setColors(Color.BLUE, Color.BLACK, Color.CYAN, Color.GREEN, Color.CYAN);
		
		while(true) {
			if(!scannedRobot) {
				scan();
			}
			if(!scannedRobot) {
				ahead(50);
			}
			if(!scannedRobot) {
				scan();
			}
			if(!scannedRobot) {
				turnLeft(20);
			}
		}
	}
	
	@Override
	public void onDeath(DeathEvent event) {
		System.out.println("Who killed me?? My revenge will be terrible!");
	}
	
	@Override
	public void onHitWall(HitWallEvent e) {
		turnLeft(95);
	}
	
	@Override
	public void onHitRobot(HitRobotEvent event) {
		if (getGunHeat() == 0) {
			setTurnLeft(event.getBearing());
			execute();
			fire(3);
			fleeAfterCollision();
		} else {
			fleeAfterCollision();
		}
	}

	private void fleeAfterCollision() {
		setBack(30);
		setTurnLeft(30);
		execute();
		if (getGunHeat() == 0) {
			fire(1);
		}
	}
	
	@Override
	public void onBulletHit(BulletHitEvent event) {
		System.out.println("bullet hit");
		if (getGunHeat() == 0) {
			fire(3);
			if(getGunHeat() == 0) {
				fire(1);
			}
			if(getGunHeat() == 0) {
				fire(1);
			}
			scan();
		} else {
			System.out.println("Damn, I'm overheating "+ getGunHeat());
			setTurnRight(5);
			setBack(50);
			execute();
		}
	}
	
	@Override
	public void onHitByBullet(HitByBulletEvent event) {
		setTurnRight(90);
		setBack(200);
		execute();
		System.out.println("touché mais pas coulé!");
	}
	
	@Override
	public void onScannedRobot(ScannedRobotEvent event) {
		scannedRobot = true;
		System.out.println("scanned robot "+ event.getDistance());
		if (event.getDistance() < 600 && getGunHeat() == 0) {
			if(event.getBearing() != 0) {
				turnLeft(event.getBearing());
			}
			fire(2);
			System.out.println("fire!");
			scan();
		}
		scannedRobot = false;
	}
	
	@Override
	public void onBulletHitBullet(BulletHitBulletEvent event) {
		if(getGunHeat() == 0) {
			fire(3);
		}
		setTurnLeft(20);
		setAhead(30);
		setTurnRight(20);
		execute();
		if(getGunHeat() == 0) {
			fire(3);
		}
	}


}
