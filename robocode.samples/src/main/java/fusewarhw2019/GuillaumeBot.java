package fusewarhw2019;


import java.awt.*;
import java.awt.event.MouseEvent;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import robocode.AdvancedRobot;
import robocode.BulletHitBulletEvent;
import robocode.BulletHitEvent;
import robocode.BulletMissedEvent;
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

import static robocode.util.Utils.normalAbsoluteAngle;
import static robocode.util.Utils.normalRelativeAngle;


/**
 * GuillaumeBot
 *
 * @author Guillaume Nodet (original)
 */
public class GuillaumeBot extends AdvancedRobot {

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
			return normalAbsoluteAngle(Math.atan2(other.x - x, other.y - y));
		}
		public double distance(Point other) {
			return Math.sqrt((other.x - x) * (other.x - x) + (other.y - y) * (other.y - y));
		}
		public Point add(Vector v) {
			return fromXY(x + v.dx, y + v.dy);
		}
		public Vector sub(Point p) {
			return Vector.fromXY(p.x - x, p.y - y);
		}

		@Override
		public String toString() {
			return "Point{" + "x=" + x + ", y=" + y + '}';
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
			dir = normalAbsoluteAngle(dir);
			return new Vector(mag * Math.sin(dir), mag * Math.cos(dir), dir, mag);
		}
		public static Vector fromXY(double dx, double dy) {
			return new Vector(dx, dy, normalAbsoluteAngle(Math.atan2(dx, dy)), Math.hypot(dx, dy));
		}

		@Override
		public String toString() {
			return "Vector{" + "dx=" + dx + ", dy=" + dy + ", d=" + d + ", m=" + m + '}';
		}
	}

	static class Robot {
		final String name;
		final boolean self;
		boolean dead;
		Point location;
		Vector velocity;
		double energy;
		long time = -1;

		public Robot(String name) {
			this(name, false);
		}

		protected Robot(String name, boolean self) {
			this.name = name;
			this.self = self;
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
				this.location = location;
				this.velocity = velocity;
				this.energy = energy;
				this.time = time;
			}
		}
	}

	static class SelfRobot extends Robot {
		double bodyHeading;
		double gunHeading;
		double gunHeat;
		double radarHeading;

		public SelfRobot(String name) {
			super(name, true);
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
					.forEach(sre -> robots.computeIfAbsent(sre.getName(), Robot::new).update(
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
					.forEach(de -> robots.computeIfAbsent(de.getName(), Robot::new).dead = true);
		}

		public boolean haveFoundAll() {
			return robots.size() >= actor.getOthers() + 1;
		}

		public List<Robot> aliveEnemies() {
			return robots.values().stream()
					.filter(Robot::isAlive)
					.filter(Robot::isEnemy)
					.collect(Collectors.toList());
		}

	}

	static class SpinRadar implements Runnable {
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
			double radarturn = normalRelativeAngle(direction - robots.self.radarHeading);
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

	static class Locking1x1Radar implements Runnable {
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
				turn = FACTOR * normalRelativeAngle(actor.getRadarHeadingRadians() - bearing);
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

	static class MeleeRadar implements Runnable {
		private final AdvancedRobot actor;
		private final Robots robots;
		private int direction;
		Robot oldest;
		double radar;
		double target;
		double bearing;
		public MeleeRadar(AdvancedRobot actor, Robots robots, int direction) {
			this.actor = actor;
			this.robots = robots;
			this.direction = direction;
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

	static class CornerMovement implements Runnable {
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

		public CornerMovement(AdvancedRobot actor, Robots robots) {
			this.actor = actor;
			this.robots = robots;
			double w = actor.getBattleFieldWidth() - 50;
			double h = actor.getBattleFieldHeight() - 50;
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
				if (locs.get(newTarget) < locs.get(closest)) {
					target = newTarget;
					goal = null;
				}
			}
			if (target == null || goTo(target)) {
				target = null;
				while (true) {
					if (goal == null) {
						double goaly = ycoords.charAt(index);
						double myy = robots.self.location.y;
						if (myy > actor.getBattleFieldHeight() / 2)
							goaly = actor.getBattleFieldHeight() - goaly;
						double goalx = xcoords.charAt(index);
						double myx = robots.self.location.x;
						if (myx > actor.getBattleFieldWidth() / 2)
							goalx = actor.getBattleFieldWidth() - goalx;
						goal = Point.fromXY(goalx, goaly);
					}
					if (goTo(goal)) {
						index = (index + 1) % PATTERN_LENGTH;
						goal = null;
						actor.out.println("Goal reached");
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
				double h = robots.self.bodyHeading;
				double a2 = Utils.normalRelativeAngle(diff.d - h);
				turn = Math.atan(Math.tan(a2));
				ahead = Math.abs(turn) > 1 ? 0 : (turn == a2 ? 1.0 : -1.0) * diff.m;
				actor.setTurnRightRadians(turn);
				actor.setAhead(ahead);
				return false;
			}
		}
		public String toString() {
			return "CornerMovement{" +
					"index=" + index +
					", target=" + target +
					", goal=" + goal +
					", ahead=" + ahead +
					", turn=" + turn +
					'}';
		}
	}

	static class Gun implements Runnable {
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
				actor.setFireBullet(power);
			} else if (robots.self.gunHeat <= 3 * actor.getGunCoolingRate() && !robots.aliveEnemies().isEmpty()) {
				double angle = computeAngle();
				power = computeBulletPower();
				turn = Utils.normalRelativeAngle(angle - robots.self.gunHeading);
				actor.setTurnGunRightRadians(turn);
			} else {
				power = 0;
				target = null;
				turn = Double.NaN;
			}
		}
		private double computeBulletPower() {
			double d = target.location.sub(robots.self.location).m;
			if (d < 150) {
				return 3.0;
			} else if (d < 250) {
				return 2.5;
			} else if (d > 700) {
				return 1.5;
			} else {
				return 2.0;
			}
		}
		private double computeAngle() {
			target = robots.robots.values().stream()
					.filter(Robot::isAlive)
					.filter(Robot::isEnemy)
					.min(Comparator.comparingDouble(r -> r.location.sub(robots.self.location).m))
					.get();
			return robots.self.location.angleTo(target.location);
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
	CornerMovement movement;
	Gun gun;
	Runnable radar;
	List<Event> events = new ArrayList<>();

	public void init() {
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
		while(true) {
			if (events.size() != 0) {
				List<Event> le = new ArrayList<>(events);
				events.clear();
				tick(le);
			}
			execute();
		}
	}

	public void tick(List<Event> events) {
		out.println("---------------------------------------------");
		robots.handleEvents(events);
		if (robots.haveFoundAll()) {
			if (robots.aliveEnemies().size() == 1 && !(radar instanceof Locking1x1Radar)) {
				radar = new Locking1x1Radar(this, robots);
			}
			if (radar instanceof SpinRadar) {
				out.println("Radar battle mode");
				radar = new MeleeRadar(this, robots, ((SpinRadar) radar).direction);
			}
			movement.run();
			gun.run();
		}
		radar.run();
		out.println("Body heading: " + getHeading());
		out.println("Gun heading: " + getGunHeading());
		out.println("Radar heading: " + getRadarHeading());
		out.println("Movement: " + movement.toString());
		out.println("Radar: " + radar.toString());
		out.println("Gun: " + gun.toString());
	}

	public void onMouseClicked(MouseEvent e) {
		movement.target = Point.fromXY(e.getX(), e.getY());
		movement.goal = null;
		movement.forced = true;
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


}
