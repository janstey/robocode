package io.cunningt;

import java.awt.Color;
import robocode.*;
import robocode.ScannedRobotEvent;
import static robocode.util.Utils.normalRelativeAngleDegrees;
import java.awt.Color;

/**
 * HappyFunBot - a robot by Tom Cunningham (http://github.com/cunningt)
 */
public class HappyFunBot extends Robot
{

	private int wallCounter = 0;
	private int moveCounter = 0;

	/**
	 * run: FooBarRobot's default behavior
	 */
	public void run() {
		// Initialization of the robot should be put here

		setBodyColor(Color.BLACK);
		setGunColor(Color.BLACK);
		setRadarColor(Color.PINK);
		setBulletColor(Color.GREEN);
		setScanColor(Color.YELLOW);

		// Robot main loop
		while(true) {
			if (wallCounter >= 2) {
				if (moveCounter < 9) {
					ahead(100);			
				} else {
					turnRight(90);
					ahead(100);
				}
				turnGunRight(180);
			} else {
				ahead(100);			
			}
		}
	}

	/**
	 * onScannedRobot: What to do when you see another robot
	 */
	public void onScannedRobot(ScannedRobotEvent e) {
		System.out.println("Scanned " + e.getName() + " robot");

		// Only start firing when we've started our route
		if (wallCounter >= 1) {
			fireAtThatBot(e.getDistance());
			scan();
			resume();
		}
	}
	
	public void fireAtThatBot(double robotDistance) {
		if (robotDistance > 200 || getEnergy() < 15) {
			fire(1);
		} else if (robotDistance > 50) {
			fire(2);
		} else {
			ahead(40);
			fire(3);
		}
	}

	/**
	 * onHitByBullet: What to do when you're hit by a bullet
	 */
	public void onHitByBullet(HitByBulletEvent e) {
	}
	
	public void onRobotDeath(RobotDeathEvent rde) {
	}

	/**
	 * onHitWall: What to do when you hit a wall
	 */
	public void onHitWall(HitWallEvent e) {
		turnRight(e.getBearing());
		turnRight(90);
		wallCounter++;
		moveCounter = 0;
	}	
}
