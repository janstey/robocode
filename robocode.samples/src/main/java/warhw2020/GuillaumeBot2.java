package warhw2020;


import java.awt.*;
import java.awt.event.MouseEvent;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import robocode.AdvancedRobot;
import robocode.BulletHitBulletEvent;
import robocode.BulletHitEvent;
import robocode.BulletMissedEvent;
import robocode.Condition;
import robocode.CustomEvent;
import robocode.DeathEvent;
import robocode.Event;
import robocode.HitByBulletEvent;
import robocode.HitRobotEvent;
import robocode.HitWallEvent;
import robocode.MessageEvent;
import robocode.RobotDeathEvent;
import robocode.Rules;
import robocode.ScannedRobotEvent;
import robocode.SkippedTurnEvent;
import robocode.StatusEvent;
import robocode.WinEvent;
import robocode.util.Utils;


/**
 * GuillaumeBot
 *
 * @author Guillaume Nodet (original)
 */
public class GuillaumeBot2 extends AdvancedRobot {

	public static double ROBOT_SIZE = 36.0;
	public static double WALL_MIN_DIST = ROBOT_SIZE / 2.0;

	static int nbRounds = 0;

	static class Point {
		final double x, y;
		private Point(double x, double y) {
			this.x = x;
			this.y = y;
		}
		public static Point fromXY(double x, double y) {
			return new Point(x, y);
		}
		public double angleTo(Point other) {
			return Utils.normalAbsoluteAngle(Math.atan2(other.x - x, other.y - y));
		}
		public double distance(Point other) {
			return Math.hypot(other.x - x, other.y - y);
		}
		public Point add(Vector v) {
			return fromXY(x + v.dx, y + v.dy);
		}
		public Point add(Vector v, double scalar) {
			return fromXY(x + v.dx * scalar, y + v.dy * scalar);
		}
		public Vector sub(Point p) {
			return Vector.fromXY(p.x - x, p.y - y);
		}

		@Override
		public String toString() {
			return String.format("Point{x=%.1f, y=%.1f}", x, y);
		}

		public double lineDist(Point p1, Point p2) {
			return Math.abs((p2.y - p1.y) * x - (p2.x - p1.x) * y + p2.x * p1.y - p2.y * p1.x) / p1.distance(p2);
		}
	}

	static class Vector {
		final double dx, dy, d, m;
		private Vector(double dx, double dy, double d, double m) {
			this.dx = dx;
			this.dy = dy;
			this.d = d;
			this.m = m;
		}
		public static Vector fromDM(double dir, double mag) {
			dir = Utils.normalAbsoluteAngle(dir);
			return new Vector(mag * Math.sin(dir), mag * Math.cos(dir), dir, mag);
		}
		public static Vector fromXY(double dx, double dy) {
			return new Vector(dx, dy, Utils.normalAbsoluteAngle(Math.atan2(dx, dy)), Math.hypot(dx, dy));
		}
		public Vector add(Vector v) {
			return Vector.fromXY(dx + v.dx, dy + v.dy);
		}

		@Override
		public String toString() {
			return String.format("Vector{dx=%.1f, dy=%.1f, d=%.1f, m=%.1f}", dx, dy, (d * 180 / Math.PI), m);
		}
	}

	static class HistoricData {
		long time;
		Point location;
		Vector velocity;
		double energy;
		double deltaHeading;

		public HistoricData(long time, Point location, Vector velocity, double energy, double deltaHeading) {
			this.time = time;
			this.location = location;
			this.velocity = velocity;
			this.energy = energy;
			this.deltaHeading = deltaHeading;
		}
	}

	static class Robot {
		final String name;
		final boolean self;
		boolean dead;
		Point location;
		Vector velocity;
		double energy;
		double deltaHeading;
		long time = -1;
		List<HistoricData> history = new ArrayList<>();
		List<VirtualGun> virtualGuns;

		public Robot(Robots robots, String name) {
			this(robots, name, false);
		}

		protected Robot(Robots robots, String name, boolean self) {
			this.name = name;
			this.self = self;
			if (robots != null) {
				this.virtualGuns = Stream.of(new HeadOn(), new Linear(), new LinearAverageVelocity(),
						new Circular(), new CircularAverageHeading(), new CircularAverageHeadingAndVelocity(),
						new CircularAverageVelocity(), new Random())
						.map(t -> new VirtualGun(t, robots, this))
						.collect(Collectors.toList());
			}
		}

		public String getName() {
			return name;
		}

		public Point getLocation() {
			return location;
		}

		public Vector getVelocity() {
			return velocity;
		}

		public double getEnergy() {
			return energy;
		}

		public long getTime() {
			return time;
		}

		public boolean isSelf() {
			return self;
		}

		public boolean isEnemy() {
			return !self;
		}

		public boolean isDead() {
			return dead;
		}

		public boolean isAlive() {
			return !dead;
		}

		void update(String name, Point location, Vector velocity, double energy, long time) {
			if (name.equals(getName()) && time > getTime()) {
				this.deltaHeading = this.time < 0 ? 0.0 : (velocity.d - this.velocity.d) / (time - this.time);
				this.location = location;
				this.velocity = velocity;
				this.energy = energy;
				this.time = time;
				this.history.add(new HistoricData(this.time, this.location, this.velocity, this.energy, this.deltaHeading));
			}
		}

		@Override
		public String toString() {
			return "Robot{" +
					"name='" + name + '\'' +
					'}';
		}

		public void fireVirtualBullet(double power) {
			virtualGuns.forEach(g -> g.fireVirtualBullet(power));
		}

		public VirtualGun getBestGun() {
			return virtualGuns.stream().max(Comparator.comparingDouble(VirtualGun::getHitRate)).get();
		}

	}

	static class SelfRobot extends Robot {
		double bodyHeading;
		double gunHeading;
		double gunHeat;
		double radarHeading;

		public SelfRobot(String name) {
			super(null, name, true);
		}

		void update(String name, Point location, Vector velocity, double energy, long time,
					double bodyHeading, double gunHeading, double gunHeat, double radarHeading) {
			super.update(name, location, velocity, energy, time);
			this.bodyHeading = bodyHeading;
			this.gunHeading = gunHeading;
			this.gunHeat = gunHeat;
			this.radarHeading = radarHeading;
		}
	}

	static class Robots {
		private final AdvancedRobot actor;
		private final Map<String, Robot> robots = new HashMap<>();
		private final SelfRobot self;

		public Robots(AdvancedRobot actor) {
			this.actor = actor;
			self = new SelfRobot(actor.getName());
			robots.put(self.name, self);
		}

		public void handleEvents(List<Event> events) {
			// Self update
			StatusEvent statusEvent = events.stream()
					.filter(StatusEvent.class::isInstance)
					.map(StatusEvent.class::cast)
					.findFirst().orElseThrow(IllegalStateException::new);
			self.update(self.getName(),
					Point.fromXY(statusEvent.getStatus().getX(), statusEvent.getStatus().getY()),
					Vector.fromDM(statusEvent.getStatus().getHeadingRadians(), statusEvent.getStatus().getVelocity()),
					statusEvent.getStatus().getEnergy(),
					statusEvent.getTime(),
					statusEvent.getStatus().getHeadingRadians(),
					statusEvent.getStatus().getGunHeadingRadians(),
					statusEvent.getStatus().getGunHeat(),
					statusEvent.getStatus().getRadarHeadingRadians());
			// Scanned robots updates
			events.stream()
					.filter(ScannedRobotEvent.class::isInstance)
					.map(ScannedRobotEvent.class::cast)
					.forEach(sre -> robots.computeIfAbsent(sre.getName(), this::newRobot).update(
							sre.getName(),
							Point.fromXY(statusEvent.getStatus().getX(), statusEvent.getStatus().getY())
									.add(Vector.fromDM(statusEvent.getStatus().getHeadingRadians() + sre.getBearingRadians(), sre.getDistance())),
							Vector.fromDM(sre.getHeadingRadians(), sre.getVelocity()),
							sre.getEnergy(),
							sre.getTime() - 1
					));
			// Robot deaths
			events.stream()
					.filter(RobotDeathEvent.class::isInstance)
					.map(RobotDeathEvent.class::cast)
					.forEach(de -> robots.computeIfAbsent(de.getName(), this::newRobot).dead = true);
		}

		private Robot newRobot(String name) {
			return new Robot(this, name);
		}

		public boolean haveFoundAll() {
			return robots.size() >= actor.getOthers() + 1;
		}

		public Stream<Robot> robots() {
			return robots.values().stream();
		}

		public List<Robot> aliveEnemies() {
			return robots()
					.filter(Robot::isAlive)
					.filter(Robot::isEnemy)
					.collect(Collectors.toList());
		}

	}

	interface Radar {
		void run();
	}

	static class SpinRadar implements Radar {
		private final AdvancedRobot actor;
		private final Robots robots;
		private int direction;
		private boolean spin = true;
		public SpinRadar(AdvancedRobot actor, Robots robots) {
			this.actor = actor;
			this.robots = robots;
		}
		public void run() {
			if (direction == 0) {
				actor.out.println("Initial radar spin");
				direction = computeInitialDirection();
			}
			if (!robots.haveFoundAll()) {
				initialSpin();
			} else {
				if (spin) {
					spin = false;
					actor.out.println("Radar battle mode");
				}
				turnRadar();
			}
		}
		private void turnRadar() {
			actor.setTurnRadarRightRadians(direction * (Rules.RADAR_TURN_RATE_RADIANS + Rules.GUN_TURN_RATE_RADIANS + Rules.MAX_TURN_RATE_RADIANS));
		}
		private void initialSpin() {
			actor.setTurnGunRightRadians(direction * Rules.MAX_TURN_RATE_RADIANS);
			actor.setTurnRightRadians(direction * (Rules.GUN_TURN_RATE_RADIANS + Rules.MAX_TURN_RATE_RADIANS));
			actor.setTurnRadarRightRadians(direction * (Rules.RADAR_TURN_RATE_RADIANS + Rules.GUN_TURN_RATE_RADIANS + Rules.MAX_TURN_RATE_RADIANS));
		}
		private int computeInitialDirection() {
			Point center = new Point(actor.getBattleFieldWidth() / 2, actor.getBattleFieldHeight() / 2);
			// Calculate the necessary radar turn
			double direction = robots.self.location.angleTo(center);
			double radarturn = Utils.normalRelativeAngle(direction - robots.self.radarHeading);
			// Choose the turn direction
			if (radarturn == 0) {
				radarturn = Math.random() - 0.5;
			}
			return (radarturn >= 0) ? 1 : -1;
		}
		@Override
		public String toString() {
			return "SpinRadar{" + "direction=" + direction + '}';
		}
	}

	static class Locking1x1Radar implements Radar {
		private static final double FACTOR = 2.1;
		private final AdvancedRobot actor;
		private final Robots robots;
		Robot target;
		double bearing;
		double turn;
		public Locking1x1Radar(AdvancedRobot actor, Robots robots) {
			this.actor = actor;
			this.robots = robots;
			target = robots.aliveEnemies().get(0);
		}
		public void run() {
			if (robots.self.time - 2 > target.time) {
				turn = Double.POSITIVE_INFINITY;
			} else {
				bearing = target.location.sub(robots.self.location).d;
				turn = FACTOR * Utils.normalRelativeAngle(actor.getRadarHeadingRadians() - bearing);
			}
			actor.setTurnRadarRightRadians(turn);
		}
		@Override
		public String toString() {
			return "Locking1x1Radar{" +
					"target=" + target.name + "(pos:" + target.location + ", vel:" + target.velocity + ")" +
					", bearing=" + Math.toDegrees(bearing) +
					", turn=" + Math.toDegrees(turn) +
					'}';
		}
	}

	static class MeleeRadar implements Radar {
		private final AdvancedRobot actor;
		private final Robots robots;
		Robot oldest;
		double radar;
		double target;
		double bearing;
		public MeleeRadar(AdvancedRobot actor, Robots robots) {
			this.actor = actor;
			this.robots = robots;
		}
		public void run() {
			radar = actor.getRadarHeadingRadians();
			Robot oldest = robots.aliveEnemies().stream()
					.filter(r -> r.location.sub(robots.self.location).m <= Rules.RADAR_SCAN_RADIUS - 100)
					.min(Comparator.comparingLong(Robot::getTime))
					.orElse(null);
			if (oldest != null && oldest != this.oldest) {
				this.oldest = oldest;
				target = oldest.location.sub(robots.self.location).d;
				bearing = Utils.normalRelativeAngle(radar - target);
				if (bearing > 0)
					actor.setTurnRadarRightRadians(Double.POSITIVE_INFINITY);
				else
					actor.setTurnRadarRightRadians(Double.NEGATIVE_INFINITY);
			}
		}

		@Override
		public String toString() {
			return "MeleeRadar{" +
					"oldest=" + (oldest != null ? oldest.name : "n/a") +
					", radar=" + radar +
					", target=" + target +
					", bearing=" + bearing +
					'}';
		}
	}

	interface Movement {
		void run();
	}

	static class Random1x1Movement implements Movement {

		private final AdvancedRobot actor;
		private final Robots robots;
		double movementLateralAngle = 0.2;
		double ahead;
		double turn;
		long lastChange = 0;

		public Random1x1Movement(AdvancedRobot actor, Robots robots) {
			this.actor = actor;
			this.robots = robots;
		}
		public void run() {
			// Change lateral direction at random
			double flattenerFactor = 0.06;
			if (Math.random() < flattenerFactor) {
				movementLateralAngle *= -1;
				lastChange = robots.self.time;
			}
			double bfw = actor.getBattleFieldWidth();
			double bfh = actor.getBattleFieldHeight();
			if (robots.aliveEnemies().isEmpty()) {
				return;
			}
			Robot enemy = robots.aliveEnemies().iterator().next();
			Point d;
			double tries = 0;
			do {
				Vector v = enemy.location.sub(robots.self.location);
				d = enemy.location.add(Vector.fromDM(v.d + movementLateralAngle, v.m * (1.1 - tries / 100.0)));
				tries++;
			} while (tries < 100 && (d.x < WALL_MIN_DIST || d.x > bfw - WALL_MIN_DIST || d.y < WALL_MIN_DIST || d.y > bfh - WALL_MIN_DIST));
			goTo(d);
		}
		private void goTo(Point p) {
			Vector diff = robots.self.location.sub(p);
			double h = robots.self.bodyHeading;
			double a2 = Utils.normalRelativeAngle(diff.d - h);
			double turn = Math.atan(Math.tan(a2));
			double ahead = Math.abs(turn) > 1 ? 0 : (turn == a2 ? 1.0 : -1.0) * diff.m;
			ahead = Math.signum(ahead) * Math.min(Math.abs(ahead), Rules.MAX_VELOCITY);
			actor.setTurnRightRadians(turn);
			actor.setAhead(ahead);
			actor.setMaxVelocity(Math.abs(actor.getTurnRemaining()) > 33 ? 0 : Rules.MAX_VELOCITY);
			if ((turn - this.turn) >= 1e-3 || (ahead - this.ahead) >= 1e-3) {
//				actor.out.printf("Moving: turning: %.1f, ahead: %.1f%n", turn * 180 / Math.PI, ahead);
				this.turn = turn;
				this.ahead = ahead;
			}
		}
	}

	static class CornerMovement implements Movement {
		static final int PATTERN_LENGTH = 8;
		//These are the coordinates of our corner movement (if it was in the lower-left corner).
		//The length of these strings should be PATTERN_LENGTH and Lib should have to change
		//directions (as in forward or reverse) for each point.
		static final String xcoords = ("" + (char)30 + (char)30 + (char)90 + (char)30 + (char)150 + (char)150 + (char)30 + (char)210);
		static final String ycoords = ("" + (char)30 + (char)210 + (char)30 + (char)150 + (char)150 + (char)30 + (char)90 + (char)30);

		private final AdvancedRobot actor;
		private final Robots robots;
		int index = 0;
		Point goal;
		double ahead;
		double turn;
		Point[] corners;
		Point target;
		boolean forced;
		double battleFieldWidth;
		double battleFieldHeight;
		Robot ramming;
		Robot avoiding;

		public CornerMovement(AdvancedRobot actor, Robots robots) {
			this.actor = actor;
			this.robots = robots;
			this.battleFieldHeight = actor.getBattleFieldHeight();
			this.battleFieldWidth = actor.getBattleFieldWidth();
			double w = battleFieldWidth - 50;
			double h = battleFieldHeight - 50;
			corners = new Point[] {
					Point.fromXY(50, 50),
					Point.fromXY(w, 50),
					Point.fromXY(w, h),
					Point.fromXY(50, h)
			};
		}

		public void run() {
			// Choose corner
			if (target == null || !forced) {
				Map<Point, Integer> locs = new HashMap<>();
				Stream.of(corners).forEach(c -> locs.put(c, 0));
				for (Robot r : robots.aliveEnemies()) {
					Point c = Stream.of(corners).min(Comparator.comparingDouble(r.location::distance)).get();
					locs.put(c, locs.get(c) + 1);
				}
				Point newTarget = Stream.of(corners).min(Comparator.comparingInt(locs::get)).get();
				Point closest = Stream.of(corners).min(Comparator.comparingDouble(robots.self.location::distance)).get();
				int diff = robots.aliveEnemies().size() >= 4 ? 1 : 0; // avoid changing if 4 enemies or more
				if (locs.get(newTarget) < locs.get(closest) - diff) {
					if (newTarget != target) {
						target = newTarget;
						goal = null;
//						actor.out.println("New target: " + target);
					}
				}
			}
			if (target == null || goTo(target)) {
				target = null;
				while (true) {
					if (goal == null) {
						double goaly = ycoords.charAt(index);
						double myy = robots.self.location.y;
						if (myy > battleFieldHeight / 2)
							goaly = battleFieldHeight - goaly;
						double goalx = xcoords.charAt(index);
						double myx = robots.self.location.x;
						if (myx > battleFieldWidth / 2)
							goalx = battleFieldWidth - goalx;
						goal = Point.fromXY(goalx, goaly);
//						actor.out.println("New goal: " + goal);
					}
					if (goTo(goal)) {
						index = (index + 1) % PATTERN_LENGTH;
						goal = null;
//						actor.out.println("Goal reached");
					} else {
						break;
					}
				}
			}
		}
		private boolean goTo(Point p) {
			Vector diff = robots.self.location.sub(p);
			if (diff.m < 10) {
				return true;
			} else {
				// Use a gravity field to avoid other robots
				final double FACTOR = 50000.0;
				Vector f = Vector.fromDM(diff.d, 10.0);
				for (Robot r : robots.aliveEnemies()) {
					Vector d = r.location.sub(robots.self.location);
					if (d.m < 100.0) {
						d = Vector.fromDM(d.d, FACTOR / (d.m * d.m));
						f = f.add(d);
					}
				}
				// Avoid walls
				Vector d = Vector.fromDM(f.d, 8.0);
				Point n = robots.self.location.add(d);
				Point m = Point.fromXY(
						Math.max(Math.min(n.x, battleFieldWidth - WALL_MIN_DIST), WALL_MIN_DIST),
						Math.max(Math.min(n.y, battleFieldHeight - WALL_MIN_DIST), WALL_MIN_DIST));
				diff = robots.self.location.sub(m);
				// Run
				double h = robots.self.bodyHeading;
				double a2 = Utils.normalRelativeAngle(diff.d - h);
				double turn = Math.atan(Math.tan(a2));
				double ahead = Math.abs(turn) > 1 ? 0 : (turn == a2 ? 1.0 : -1.0) * diff.m;
				ahead = Math.signum(ahead) * Math.min(Math.abs(ahead), Rules.MAX_VELOCITY);
				actor.setTurnRightRadians(turn);
				actor.setAhead(ahead);
				if ((turn - this.turn) >= 1e-3 || (ahead - this.ahead) >= 1e-3) {
//					actor.out.printf("Moving: turning: %.1f, ahead: %.1f%n", turn * 180 / Math.PI, ahead);
					this.turn = turn;
					this.ahead = ahead;
				}
				return false;
			}
		}
		public String toString() {
			return "CornerMovement{" +
					"index=" + index +
					", target=" + target +
					", goal=" + goal +
					", ramming=" + (ramming != null ? ramming.name : "null") +
					", avoiding=" + (avoiding != null ? avoiding.name : "null") +
					", ahead=" + ahead +
					", turn=" + turn +
					'}';
		}
	}

	interface Targeting {
		void init(Robots robots, Robot enemy);
		double computeAngle(double firePower);
	}

	static abstract class FastTargeting implements Targeting {

		Robots robots;
		Robot enemy;

		public void init(Robots robots, Robot enemy) {
			this.robots = robots;
			this.enemy = enemy;
		}

		double doCompute(double firePower, double deltaHeading, double deltaSpeed) {
			firePower = Math.max(Math.min(Math.min(robots.self.energy, firePower),
					Rules.MAX_BULLET_POWER), Rules.MIN_BULLET_POWER);
			double bulletSpeed = Rules.getBulletSpeed(firePower);
			Point m = robots.self.location;
			Point e = enemy.location;
			double eH = enemy.velocity.d;
			double minX = WALL_MIN_DIST, minY = WALL_MIN_DIST,
					maxX = (int) robots.actor.getBattleFieldWidth() - WALL_MIN_DIST,
					maxY = (int) robots.actor.getBattleFieldHeight() - WALL_MIN_DIST;
			for (int t = -1; t * bulletSpeed < m.distance(e); t++) {
				Point newE = e.add(Vector.fromDM(eH, deltaSpeed));
				eH += deltaHeading;
				if (newE.x < minX || newE.y < minY || newE.x > maxX || newE.y > maxY) {
					if (deltaHeading == 0.0) {
						break;
					}
				} else {
					e = newE;
				}
			}
			return m.sub(e).d;
		}
	}

	static class HeadOn extends FastTargeting {
		@Override
		public double computeAngle(double firePower) {
			return robots.self.location.sub(enemy.location).d;
		}
	}

	static class Linear extends FastTargeting {
		@Override
		public double computeAngle(double firePower) {
			return doCompute(firePower, 0.0, enemy.velocity.m);
		}
	}

	static class LinearAverageVelocity extends FastTargeting {
		@Override
		public double computeAngle(double firePower) {
			double avgVel = lastN(enemy.history, 10).stream().mapToDouble(h -> h.velocity.m).average().getAsDouble();
			return doCompute(firePower, 0.0, avgVel);
		}
	}

	static class Circular extends FastTargeting {
		@Override
		public double computeAngle(double firePower) {
			return doCompute(firePower, enemy.deltaHeading, enemy.velocity.m);
		}
	}

	static class CircularAverageHeading extends FastTargeting {
		@Override
		public double computeAngle(double firePower) {
			double avgHead = lastN(enemy.history, 10).stream().mapToDouble(h -> h.deltaHeading).average().getAsDouble();
			return doCompute(firePower, avgHead, enemy.velocity.m);
		}
	}

	static class CircularAverageHeadingAndVelocity extends FastTargeting {
		@Override
		public double computeAngle(double firePower) {
			double avgHead = lastN(enemy.history, 10).stream().mapToDouble(h -> h.deltaHeading).average().getAsDouble();
			double avgVel = lastN(enemy.history, 10).stream().mapToDouble(h -> h.velocity.m).average().getAsDouble();
			return doCompute(firePower, avgHead, avgVel);
		}
	}

	static class CircularAverageVelocity extends FastTargeting {
		@Override
		public double computeAngle(double firePower) {
			double avgVel = lastN(enemy.history, 10).stream().mapToDouble(h -> h.velocity.m).average().getAsDouble();
			return doCompute(firePower, enemy.deltaHeading, avgVel);
		}
	}

	static class Random extends FastTargeting {
		@Override
		public double computeAngle(double firePower) {
			double angle = robots.self.location.sub(enemy.location).d;
			double delta = Math.asin(Rules.MAX_VELOCITY / Rules.getBulletSpeed(firePower));
			return angle + Math.random() * (delta * 2.0) - delta;
		}
	}

	static class VirtualBullet {
		final Robot enemy;
		final Point from;
		final Vector speed;
		final long time;

		public VirtualBullet(Robot enemy, Point from, double angle, double firePower, long time) {
			this.enemy = enemy;
			this.from = from;
			this.speed = Vector.fromDM(angle, Rules.getBulletSpeed(firePower));
			this.time = time;
		}
		public boolean testHit(long time) {
			return enemy.location.distance(from.add(speed, time - this.time)) <= ROBOT_SIZE / 2.0;
		}

		public boolean testMiss(long time) {
			return from.distance(from.add(speed, time - this.time)) > from.distance(enemy.location) + ROBOT_SIZE;
		}
	}

	static Map<String, Map<String, long[]>> HITS = new HashMap<>();

	static class VirtualGun {
		final Targeting targeting;
		final Robots robots;
		final Robot enemy;
		List<VirtualBullet> bullets = new ArrayList<>();

		public VirtualGun(Targeting targeting, Robots robots, Robot enemy) {
			this.targeting = targeting;
			this.robots = robots;
			this.enemy = enemy;
			this.robots.actor.addCustomEvent(new Condition() {
				@Override
				public boolean test() {
					updateBullets();
					return false;
				}
			});
			this.targeting.init(robots, enemy);
		}

		public void fireVirtualBullet(double firePower) {
			bullets.add(new VirtualBullet(enemy, robots.self.location,
					targeting.computeAngle(firePower), firePower, robots.self.time));
		}

		public double getHitRate() {
			long[] data = HITS.computeIfAbsent(enemy.name, n -> new HashMap<>())
					.computeIfAbsent(targeting.getClass().getSimpleName(), n -> new long[2]);
			long hits = data[0];
			long fired = data[1];
			return fired == 0 ? 0.0 : (double) hits / (double) fired;
		}

		public Targeting getTargeting() {
			return targeting;
		}

		void updateBullets() {
			if (enemy.isAlive()) {
				long t = robots.actor.getTime();
				Iterator<VirtualBullet> it = bullets.iterator();
				while (it.hasNext()) {
					VirtualBullet bullet = it.next();
					if (bullet.testHit(t)) {
						long[] data = HITS.computeIfAbsent(enemy.name, n -> new HashMap<>())
								.computeIfAbsent(targeting.getClass().getSimpleName(), n -> new long[2]);
						data[0]++;
						data[1]++;
						if (data[1] > 1000) {
							data[0] /= 2;
							data[1] /= 2;
						}
						it.remove();
					} else if (bullet.testMiss(t)) {
						long[] data = HITS.computeIfAbsent(enemy.name, n -> new HashMap<>())
								.computeIfAbsent(targeting.getClass().getSimpleName(), n -> new long[2]);
						data[1]++;
						if (data[1] > 1000) {
							data[0] /= 2;
							data[1] /= 2;
						}
						it.remove();
					}
				}
			}
		}
	}

	static class Gun {
		private final AdvancedRobot actor;
		private final Robots robots;
		double power = 0;
		Robot target;
		double turn;
		public Gun(AdvancedRobot actor, Robots robots) {
			this.actor = actor;
			this.robots = robots;
		}
		public void run() {
			if (power != 0 && actor.getGunTurnRemainingRadians() == 0 && actor.getGunHeat() == 0) {
				for (Robot r : robots.aliveEnemies()) {
					r.fireVirtualBullet(computeBulletPower(r));
				}
				actor.setFireBullet(power);
//				target.fireVirtualBullet(power);
				actor.out.println("Firing at " + target + " using " + target.getBestGun().getTargeting().getClass().getSimpleName() + " with hit rate = " + Math.round(target.getBestGun().getHitRate() * 100) + "%");
			} else if (robots.self.gunHeat <= 3 * actor.getGunCoolingRate() && !robots.aliveEnemies().isEmpty()) {
				chooseTarget();
				power = computeBulletPower(target);
				double angle = computeAngle(power);
				turn = Utils.normalRelativeAngle(angle - robots.self.gunHeading);
				actor.setTurnGunRightRadians(turn);
			} else {
				power = 0;
				target = null;
				turn = Double.NaN;
			}
		}
		private double computeBulletPower(Robot target) {
			double maxFireDistance = 200.0;
			double firepower = (maxFireDistance * 3) / target.location.distance(robots.self.location);
			int nbEnemies = robots.aliveEnemies().size();
			if (nbEnemies > 1) {
				double walls = (robots.actor.getBattleFieldHeight() + robots.actor.getBattleFieldWidth()) / 2.0;
				firepower *= distToWall(robots.self.gunHeading) / walls * nbEnemies;
			} else if (nbEnemies == 1) {
				firepower = (maxFireDistance * 3) / target.location.distance(robots.self.location);
				if (target.getBestGun().getHitRate() >= 0.25) {
					firepower *= target.getBestGun().getHitRate() * 4;
				}
				if (robots.self.energy < 32) {
					firepower *= Math.min(robots.self.energy / target.energy, 1);
				}
			}
			if (target.getBestGun().getHitRate() >= 0.5) {
				firepower *= Rules.MAX_BULLET_POWER;
			}
			firepower = Math.min(firepower, target.energy / 4);
			return Math.max(Math.min(Rules.MAX_BULLET_POWER, firepower), Rules.MIN_BULLET_POWER);
		}

		private double distToWall(double a) {
			a = Utils.normalAbsoluteAngle(a);
			double bfh = robots.actor.getBattleFieldHeight();
			double bfw = robots.actor.getBattleFieldWidth();
			double wallDist = bfh - robots.self.location.y - WALL_MIN_DIST;
			if (a < robots.self.location.angleTo(Point.fromXY(bfw, bfh))) {
			} else if (a < robots.self.location.angleTo(Point.fromXY(bfw, 0.0))) {
				a -= 0.5 * Math.PI;
				wallDist = bfw - robots.self.location.x - WALL_MIN_DIST;
			} else if (a < robots.self.location.angleTo(Point.fromXY(0.0, 0.0))) {
				a -= 1.0 * Math.PI;
				wallDist = robots.self.location.y - WALL_MIN_DIST;
			} else if (a < robots.self.location.angleTo(Point.fromXY(0.0, bfh))) {
				a -= 1.5 * Math.PI;
				wallDist = robots.self.location.x - WALL_MIN_DIST;
			}
			a = Utils.normalRelativeAngle(a);
			return wallDist / Math.cos(Math.abs(a));
		}

		private double computeAngle(double power) {
			return target.getBestGun().getTargeting().computeAngle(power);
		}
		private void chooseTarget() {
			Map<Robot, Double> evals = robots.aliveEnemies().stream()
					.collect(Collectors.toMap(Function.identity(), this::targetEvaluation));
			Robot target = evals.entrySet().stream()
					.min(Comparator.comparingDouble(Map.Entry::getValue))
					.map(Map.Entry::getKey).orElse(null);
			if (target != this.target) {
//				if (target != null) {
//					actor.out.println("Gun targetting: " + target.name + " at " + target.location);
//				} else {
//					actor.out.println("No target");
//				}
				this.target = target;
			}
		}

		private double targetEvaluation(Robot robot) {
			double bfh = actor.getBattleFieldHeight();
			double bfw = actor.getBattleFieldWidth();
			double dist = robot.location.distance(robots.self.location) / Math.sqrt((bfh - WALL_MIN_DIST * 2.0) * (bfw - WALL_MIN_DIST * 2.0));
			double wall = (Math.min(robot.location.x, bfw - robot.location.x) - WALL_MIN_DIST) / (bfw / 2.0 - WALL_MIN_DIST)
					* (Math.min(robot.location.y, bfh - robot.location.y) - WALL_MIN_DIST) / (bfh / 2.0 - WALL_MIN_DIST);
			double nrj = robot.energy / 100.0;
			double gun = 1.0 - robot.getBestGun().getHitRate();
			return Math.floor(Math.sqrt(dist) * 4) * 1 + wall * wall * 0 + Math.floor(Math.sqrt(nrj) * 4) * 1 + Math.floor(Math.sqrt(gun) * 10) * 1;
		}

		private Optional<Robot> getTarget(List<Robot> possible, double m) {
			return possible.stream()
					.filter(r -> r.location.sub(robots.self.location).m < m)
					.min(Comparator.comparing(Robot::getEnergy));
		}

		@Override
		public String toString() {
			return "Gun{" +
					"target=" + (target != null ? target.name : "n/a") +
					", power=" + power +
					", turn=" + turn +
					'}';
		}
	}

	Robots robots;
	Movement movement;
	Gun gun;
	Radar radar;
	List<Event> events = new ArrayList<>();

	public void init() {
		setAllColors(Color.MAGENTA);

		nbRounds++;
		out.println("Round: " + nbRounds);

		setAdjustGunForRobotTurn(true);
		setAdjustRadarForRobotTurn(true);
		setAdjustRadarForGunTurn(true);
		setScanColor(Color.MAGENTA);

		robots = new Robots(this);
		radar = new SpinRadar(this, robots);
		movement = new CornerMovement(this, robots);
		gun = new Gun(this, robots);
	}

	public void run() {
		init();
		while (true) {
			if (events.size() != 0) {
				List<Event> le = new ArrayList<>(events);
				events.clear();
				tick(le);
			}
			execute();
		}
	}

	public void tick(List<Event> events) {
		//out.println("---------------------------------------------");
		robots.handleEvents(events);
		if (robots.haveFoundAll()) {
			if (robots.aliveEnemies().size() == 1 && !(radar instanceof Locking1x1Radar)) {
				out.println("Using Locking1x1Radar");
				radar = new Locking1x1Radar(this, robots);
			}
			if (radar instanceof SpinRadar) {
				out.println("Radar battle mode");
				radar = new MeleeRadar(this, robots);
			}
			if (robots.aliveEnemies().size() == 1 && !(movement instanceof Random1x1Movement)) {
				out.println("Using Random1x1Movement");
				movement = new Random1x1Movement(this, robots);
			}
			movement.run();
			gun.run();
		}
		radar.run();
//		out.println("Body heading: " + getHeading());
//		out.println("Gun heading: " + getGunHeading());
//		out.println("Radar heading: " + getRadarHeading());
//		out.println("Movement: " + movement.toString());
//		out.println("Radar: " + radar.toString());
//		out.println("Gun: " + gun.toString());
	}

	public void onMouseClicked(MouseEvent e) {
		if (movement instanceof CornerMovement) {
			CornerMovement cm = (CornerMovement) movement;
			cm.target = Point.fromXY(e.getX(), e.getY());
			cm.goal = null;
			cm.forced = true;
		}
	}

	public void onCustomEvent(CustomEvent arg0)                 { events.add(arg0); }
	public void onMessageReceived(MessageEvent arg0)            { events.add(arg0); }
	public void onBulletHit(BulletHitEvent arg0)                { events.add(arg0); }
	public void onBulletHitBullet(BulletHitBulletEvent arg0)    { events.add(arg0); }
	public void onBulletMissed(BulletMissedEvent arg0)          { events.add(arg0); }
	public void onDeath(DeathEvent arg0)                        { events.add(arg0); }
	public void onHitByBullet(HitByBulletEvent arg0)            { events.add(arg0); }
	public void onHitRobot(HitRobotEvent arg0)                  { events.add(arg0); }
	public void onHitWall(HitWallEvent arg0)                    { events.add(arg0); }
	public void onRobotDeath(RobotDeathEvent arg0)              { events.add(arg0); }
	public void onScannedRobot(ScannedRobotEvent arg0)          { events.add(arg0); }
	public void onStatus(StatusEvent arg0)                      { events.add(arg0); }
	public void onWin(WinEvent arg0)                            { events.add(arg0); }
	public void onSkippedTurn(SkippedTurnEvent arg0)            {
		events.add(arg0);
		out.println("WARNING! Turn skipped!");
	}


	private static <T> List<T> lastN(List<T> list, int n) {
		return list.subList(Math.max(0, list.size() - n), list.size());
	}

}
