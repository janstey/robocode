package warhw2024;

import java.awt.*;
import java.awt.event.KeyEvent;
import java.awt.geom.Arc2D;
import java.awt.geom.Line2D;
import java.awt.geom.Rectangle2D;
import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.OptionalDouble;
import java.util.Set;
import java.util.function.*;
import java.util.stream.Collectors;
import java.util.stream.DoubleStream;
import java.util.stream.IntStream;
import java.util.stream.LongStream;
import java.util.stream.Stream;

import robocode.AdvancedRobot;
import robocode.Bullet;
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
import robocode.KeyPressedEvent;
import robocode.KeyReleasedEvent;
import robocode.KeyTypedEvent;
import robocode.MessageEvent;
import robocode.RobotDeathEvent;
import robocode.Rules;
import robocode.ScannedRobotEvent;
import robocode.SkippedTurnEvent;
import robocode.StatusEvent;
import robocode.WinEvent;
import robocode.util.Utils;

import static java.lang.Math.*;
import static robocode.util.Utils.*;


/**
 * LaserToaster
 *
 * @author Guillaume Nodet (original)
 */
@SuppressWarnings("unused")
public class LaserToaster extends AdvancedRobot {

    public static double ROBOT_SIZE = 36.0;
    public static double WALL_MIN_DIST = ROBOT_SIZE / 2.0;

    public static final double NEAR_DELTA = .00001;

    public static final String DEFAULT_AIM = "#default#";
    public static final int DESCRIPTOR_SIZE = 10;

    public static double MAX_X;
    public static double MAX_Y;
    public static Rect BATTLEFIELD;
    public static double GUN_COOLING_RATE;

    static int nbRounds = 0;

    static final Map<String, Map<String, KDTree.WeightedManhattan<MeleeScan>>> MOVE_TREES = new HashMap<>();

    static KDTree<MeleeScan> getMoveTree(String firer, String target) {
        return MOVE_TREES.computeIfAbsent(firer, n -> new HashMap<>())
                .computeIfAbsent(target, n -> new KDTree.WeightedManhattan<>(DESCRIPTOR_SIZE));
    }

    static class Wave {
        final Robot firer;
        final long timeMin;
        final long timeMax;
        final double energy;
        final double bulletSpeed;
        final double[] bins;
        final double[] botShadowBins;
        boolean needRecalc;

        Wave(Robot firer, long timeMin, long timeMax, double energy) {
            this.firer = firer;
            this.timeMin = timeMin;
            this.timeMax = timeMax;
            this.energy = energy;
            this.bulletSpeed = Rules.getBulletSpeed(energy);
            this.bins = new double[360];
            this.botShadowBins = new double[360];
            Arrays.fill(botShadowBins, 1.0);
            needRecalc = true;
        }

        public double[] calcDangers(Point myLocation) {
            if (!needRecalc) {
                return bins;
            }
            Arrays.fill(bins, 0.0);
            Point fireLocation = firer.getLocation(timeMin);
            if (fireLocation == null) {
                return bins;
            }
            needRecalc = false;
            firer.others().filter(Robot::isAlive).forEach(target -> {
                Point targetLocation = target.getLocation(timeMin);
                Vector targetVelocity = target.getVelocity(timeMin);
                if (targetLocation != null && targetVelocity != null) {
                    Vector targetToFire = fireLocation.sub(targetLocation);
                    double targetBearing = targetToFire.d;
                    double latVel = targetVelocity.m * Math.sin(targetVelocity.d - targetBearing);
                    double meBearing = absoluteBearing(fireLocation, myLocation);

                    double MEA = maxEscapeAngle(bulletSpeed);
                    if (Math.abs(Utils.normalRelativeAngle(targetBearing - meBearing)) > 3 * MEA)
                        return;

                    double GFcorrection = Math.signum(latVel) * MEA;
                    double botWeight = 1.0 / sqr(targetToFire.m);
                    double[] rbins = new double[360];
                    double[] descriptor = target.targetDescriptor(this);
                    for (int k = 0; k < 2; k++) {
                        KDTree<MeleeScan> tree = firer.getMoveTree(k == 0 ? target.name : DEFAULT_AIM);
                        List<KDTree.SearchResult<MeleeScan>> cluster = tree.nearestNeighbours(
                                descriptor,
                                Math.min(10, tree.size())
                        );
                        if (!cluster.isEmpty()) {
                            double clusterDistance = cluster.stream().mapToDouble(KDTree.SearchResult::getDistance).sum() / cluster.size();
                            double weight = botWeight * Math.exp(-k);
                            for (KDTree.SearchResult<MeleeScan> v : cluster) {
                                double fireAngle = Utils.normalAbsoluteAngle(v.payload.GF * GFcorrection + targetBearing);
                                if (Math.abs(Utils.normalRelativeAngle(fireAngle - meBearing)) < 2 * MEA) {
                                    MeleeStrategy.smoothAround(rbins, ((int) (fireAngle * (180 / Math.PI))) % 360,
                                            18, v.payload.weight * weight * Math.exp(-0.5 * sqr(v.distance / clusterDistance)));
                                }
                            }
                        }
                    }

                    normalizeArea(rbins);
                    for (int i = 0; i < rbins.length; i++)
                        bins[i] += botWeight * rbins[i];
                } else {
                    needRecalc = true;
                }
            });
            normalizeArea(bins);
            return bins;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Wave wave = (Wave) o;
            return timeMin == wave.timeMin &&
                    timeMax == wave.timeMax &&
                    Double.compare(wave.energy, energy) == 0;
        }

        @Override
        public int hashCode() {
            return Objects.hash(timeMin, timeMax, energy);
        }

    }

    static class MeleeScan {
        final double GF;
        final double weight;

        public MeleeScan(double GF, double weight) {
            this.GF = GF;
            this.weight = weight;
        }
    }

    class Robot {
        final Robots robots;
        final String name;
        final boolean self;
        long death;
        Point location;
        Vector velocity;
        double energy;
        double deltaHeading;
        long time = -1;
        List<Data> history = new LinkedList<>();
        List<Wave> waves = new ArrayList<>();
        List<Wave> historicWaves = new ArrayList<>();
        double heat;
        long lastWaveCheck;
        List<VirtualGun> virtualGuns;

        public Robot(Robots robots, String name) {
            this(robots, name, false);
        }

        protected Robot(Robots robots, String name, boolean self) {
            this.robots = robots;
            this.name = name;
            this.self = self;
            this.virtualGuns = Stream.of(/*new HeadOn(),*/ new Linear(), new LinearAverageVelocity(),
                            new Circular(), new CircularAverageHeading(), new CircularAverageHeadingAndVelocity(),
                            new CircularAverageVelocity()/*, new Random()*/)
                    .map(t -> new VirtualGun(t, robots, this))
                    .collect(Collectors.toList());
            KDTree<MeleeScan> tree = getMoveTree(DEFAULT_AIM);
            if (tree.size() == 0) {
                tree.addPoint(new double[DESCRIPTOR_SIZE], new MeleeScan(0.0, 1e-20));
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
            return death > 0;
        }

        public boolean isAlive() {
            return death == 0;
        }

        void update(String name, Point location, Vector velocity, double energy, long time) {
            if (name.equals(getName()) && time > getTime()) {
                long deltaTime = time - this.time;
//				if (deltaTime > 1 && !history.isEmpty()) {
//					Data start = new Data(this.time, this.location, this.velocity);
//					Data end = new Data(time, location, velocity);
//					List<Data> datas = MovementInterpolator.interpolate(start, end);
//					if (datas != null) {
//						history.addAll(datas);
//					} else {
//						printf("Unable to interpolate for %s%n", name);
//					}
//				}

                this.deltaHeading = this.time < 0 ? 0.0 : (velocity.d - this.velocity.d) / (time - this.time);
                this.location = location;
                this.velocity = velocity;
                this.energy = energy;
                this.time = time;
                this.heat = roundComputeErrors(history.isEmpty()
                        ? robots.actor.getGunHeat()
                        : Math.max(heat - deltaTime * GUN_COOLING_RATE, 0.0));
                this.history.add(0, new Data(time, location, velocity, energy, heat, deltaHeading));
				/*
				// if energy has not changed, we know the heat (unless a bullet has been fired while hitting a wall
				if (between(Rules.MIN_BULLET_POWER, deltaEnergy, Rules.MAX_BULLET_POWER)) {
					long waveTime = time - 1;
					Wave w = new Wave(getLocation(waveTime), waveTime + 1, deltaEnergy);
					waves.add(w);
					heat += Rules.getGunHeat(w.energy);
					printf("New wave detected for %s", name);
				} else if (deltaEnergy > 0.0) {§
					printf("Energy drop of %.1f ignored%n", deltaEnergy);
				}
			 	*/
            }
        }

        public void interpolate() {
            if (history.size() >= 2) {
                Data cur = history.get(0);
                Data prv = history.get(1);
                if (cur.scan && prv.scan && cur.time == time) {
                    // Check collision
                    double deltaEnergy = cur.energy - cur.energy;
                    if (deltaEnergy != 0.0) {
                        List<Robot> candidates = new ArrayList<>();
                        for (Robot r : robots.robots.values()) {
                            if (r == this) {
                                continue;
                            }
                            for (long time = prv.time + 1; time <= cur.time; time++) {
                                if (r.getEnergyDrop(time) == 0.0) {
                                    continue;
                                }
                                Point l = r.getLocation(time);
                                Point c = this.getLocation(time);
                                if (l != null && c != null) {
                                    double d = l.distance(c);
                                    if (d < 50) {
                                        candidates.add(r);
                                    }
                                }
                            }
                        }
                    }
                    // Interpolate
                    List<Data> datas = MovementInterpolator.interpolate(prv, cur);
                    if (datas != null) {
                        history.remove(0);
                        for (Data data : datas.subList(1, datas.size())) {
                            history.add(0, data);
                        }
                    } else {
                        printf("Unable to interpolate for %s between %d and %d", name, prv.time, cur.time);
                        datas = MovementInterpolator.interpolate(prv, cur);
                    }
                }
            }
        }

        public void updateWaves() {
            long minTime = robots.robots().mapToLong(Robot::getTime).min().orElse(0);
            while (lastWaveCheck < minTime) {
                lastWaveCheck++;
                double energyBonus = -getEnergyDrop(lastWaveCheck);
                if (energyBonus > 0) {
                    Map<Wave, Set<Robot>> candidates = findWaveCandidates(lastWaveCheck);
                    if (candidates.size() == 1) {
                        Wave w = candidates.keySet().iterator().next();
                        double b = Rules.getBulletHitBonus(w.energy);
                        double d = Rules.getBulletDamage(w.energy);
                        Set<Robot> targets = candidates.values().stream().flatMap(Set::stream)
                                .collect(Collectors.toSet());
                        if (targets.size() == 1) {
                            Robot hit = targets.iterator().next();
                            printf("Wave fired at (%d-%d) by %s hit %s", w.timeMin, w.timeMax, name, hit.getName());
                            this.energy -= b; // we do substract so that we can compare with the previous for fire
                            hit.energy += d;
                            logWaveHit(w, hit);
                        } else {
                            printf("Wave fired at (%d-%d) by %s hit one of (%s)", w.timeMin, w.timeMax, name,
                                    targets.stream().map(Robot::getName).collect(Collectors.joining(",")));
                        }
                        waves.remove(w);
                        historicWaves.add(w);
                    } else if (candidates.size() > 1) {
                        printf("Wave candidates for energy gain of %.1f hitting robot %s:%n%s",
                                energyBonus, this.name,
                                candidates.entrySet().stream()
                                        .map(e -> String.format("    wave fired at (%d-%d) with energy %.1f hitting (%s)%n",
                                                e.getKey().timeMin, e.getKey().timeMax, e.getKey().energy,
                                                e.getValue().stream().map(Robot::getName).collect(Collectors.joining(","))))
                                        .collect(Collectors.joining()));
                    } else {
                        printf("Could not find matching wave for energy gain of %.1f for robot %s",
                                energyBonus, this.name);
                        findWaveCandidates(lastWaveCheck);
                    }
                }
            }
			/*
			ExtData cur = null;
			ExtData prv = null;
			for (int i = history.size() - 1; i >= 0; i--) {
				Data d = history.get(i);
				if (d instanceof ExtData) {
					if (cur == null) {
						cur = (ExtData) d;
					} else if (prv == null) {
						prv = (ExtData) d;
					} else {
						break;
					}
				}
			}

			// Check if the robot hit someone
			if (cur != null && prv != null) {
				if (cur.energy > prv.energy) {
					Map<Wave, Set<Robot>> candidates = findWaveCandidates(lastWaveCheck);
					if (candidates.size() == 1) {
						Wave w = candidates.keySet().iterator().next();
						double b = Rules.getBulletHitBonus(w.energy);
						double d = Rules.getBulletDamage(w.energy);
						Set<Robot> targets = candidates.values().stream().flatMap(Set::stream)
								.collect(Collectors.toSet());
						if (targets.size() == 1) {
							Robot hit = targets.iterator().next();
							printf("Wave fired at (%d-%d) by %s hit %s", w.timeMin, w.timeMax, name, hit.getName());
							this.energy -= b; // we do substract so that we can compare with the previous for fire
							hit.energy += d;
						} else {
							printf("Wave fired at (%d-%d) by %s hit one of (%s)", w.timeMin, w.timeMax, name,
									targets.stream().map(Robot::getName).collect(Collectors.joining(",")));
						}
						waves.remove(w);
						historicWaves.add(w);
					} else if (candidates.size() > 1) {
						printf("Wave candidates for energy gain of %.1f hitting robot %s:%n%s",
								cur.energy - prv.energy, this.name,
								candidates.entrySet().stream()
									.map(e -> String.format("    wave fired at (%d-%d) with energy %.1f hitting (%s)%n",
											e.getKey().timeMin, e.getKey().timeMax, e.getKey().energy,
											e.getValue().stream().map(Robot::getName).collect(Collectors.joining(","))))
									.collect(Collectors.joining()));
					} else {
						printf("Could not find matching wave for energy gain of %.1f for robot %s",
								cur.energy - prv.energy, this.name);
						findWaveCandidates(lastWaveCheck);
					}
				}
			}
			 */
        }

        private void logWaveHit(Wave wave, Robot hit) {
            Point fireLocation = getLocation(wave.timeMin);
            Point firedTargetLocation = hit.getLocation(wave.timeMin);
            Vector firedTargetVelocity = hit.getVelocity(wave.timeMin);
            double fireBearing = absoluteBearing(fireLocation, firedTargetLocation);
            double hitBearing = absoluteBearing(fireLocation, hit.location);
            double offset = Utils.normalRelativeAngle(hitBearing - fireBearing);

            double latVel = firedTargetVelocity.m * Math.sin(firedTargetVelocity.d - fireBearing);
            double GF = offset * Math.signum(latVel) / maxEscapeAngle(wave.bulletSpeed);
            if (GF > 1 || GF < -1)
                return;

            MeleeScan ms = new MeleeScan(GF, Math.exp(-2.0));

            double[] targetDescriptor = hit.targetDescriptor(wave);
            getMoveTree(hit.name).addPoint(targetDescriptor, ms);
            getMoveTree(DEFAULT_AIM).addPoint(targetDescriptor, ms);
            wave.firer.waves.forEach(w -> w.needRecalc = true);
        }

        private Map<Wave, Set<Robot>> findWaveCandidates(long time) {
            Data cur = null;
            Data prv = null;
            for (Data d : history) {
                if (d.scan) {
                    if (d.time >= time) {
                        cur = d;
                    } else {
                        prv = d;
                        break;
                    }
                }
            }
            if (cur == null || prv == null) {
                return Collections.emptyMap();
            }

            List<Robot> others = robots.robots()
                    .filter(r -> r != Robot.this)
                    .filter(Robot::isAlive)
                    .collect(Collectors.toList());
            Map<Wave, Set<Robot>> candidates = new HashMap<>();
            for (Wave w : waves) {
                double v = w.bulletSpeed;
                double b = Rules.getBulletHitBonus(w.energy);
                double d = Rules.getBulletDamage(w.energy);
                for (long fireTime = w.timeMin; fireTime <= w.timeMax; fireTime++) {
                    for (long hitTime = cur.time; hitTime > prv.time; hitTime--) {
                        for (Robot r : others) {
//                            if (r.getEnergyDrop(hitTime) > 0 || r.getEnergyDrop(hitTime + 1) > 0) {
                                Point l = r.getLocation(hitTime - 1);
                                if (l != null) {
                                    double dist = l.sub(getLocation(fireTime - 1)).m;
                                    if (Math.abs(dist - v * (hitTime - fireTime + 1)) <= 50) {
                                        candidates.computeIfAbsent(w, wave -> new HashSet<>()).add(r);
                                    }
                                }
//                            }
                        }
                    }
                }
            }
            return candidates;
        }

        public void createNewWaves() {
            Data cur = null;
            Data prv = null;
            for (Data d : history) {
                if (d.scan) {
                    if (cur == null) {
                        cur = d;
                    } else {
                        prv = d;
                        break;
                    }
                }
            }

            // Check if the robot has fired
            if (cur != null && prv != null && cur.time == time) {
                double deltaEnergy = roundComputeErrors(prv.energy - energy);
                if (between(Rules.MIN_BULLET_POWER, deltaEnergy, Rules.MAX_BULLET_POWER)) {
                    if (isNear(heat, 0.0)) {
                        // TODO: it could have been fired earlier, check the heat
                        long heatDelay = Math.round((prv.heat - NEAR_DELTA) / GUN_COOLING_RATE);
                        Wave w = new Wave(this, prv.time + Math.max(1, heatDelay), cur.time, deltaEnergy);
                        waves.add(w);
                        heat = Rules.getGunHeat(w.energy) - (w.timeMax - w.timeMin) * GUN_COOLING_RATE;
                        energy += w.energy;
//						printf("New wave detected for %s", name);
                    } else {
                        printf("Collision detected for %s ? (heat was %.1f)", name, heat);
                    }
                } else if (deltaEnergy > NEAR_DELTA) {
                    printf("Energy drop of %.1f ignored for %s", deltaEnergy, name);
                }
            }
        }

        void dropOldWaves() {
            // Remove old waves
            double max = Math.hypot(MAX_X, MAX_Y);
            List<Wave> old = waves.stream()
                    .filter(w -> (time - w.timeMax) * w.bulletSpeed > max)
                    .collect(Collectors.toList());
            waves.removeAll(old);
            historicWaves.addAll(old);
        }

        double getEnergyDrop(long time) {
            Data prev = null, next = null;
            for (Data data : history) {
                if (data.scan) {
                    if (data.time < time) {
                        prev = data;
                        break;
                    } else if (next == null || next.time > data.time) {
                        next = data;
                    }
                }
            }
            if (prev != null && next != null) {
                return prev.energy - next.energy;
            }
            return Double.NaN;
        }

        Point getLocation(long time) {
            if (time > this.time) {
                return null;
            } else if (time == this.time) {
                return location;
            } else {
                Data prev = null, next = null;
                for (Data data : history) {
                    if (data.time < time) {
                        if (prev == null || prev.time < data.time) {
                            prev = data;
                        }
                    } else if (data.time == time) {
                        return data.location;
                    } else {
                        if (next == null || next.time > data.time) {
                            next = data;
                        }
                    }
                }
                if (prev == null && next == null) {
                    return null;
                } else if (prev == null) {
                    return next.location.add(next.velocity, time - next.time);
                } else if (next == null) {
                    return prev.location.add(prev.velocity, time - prev.time);
                } else {
                    // use linear interpolation, we should be able to do better by using the velocity
                    return prev.location.add(prev.location.sub(next.location), ((double) time - prev.time) / (next.time - prev.time));
                }
            }
        }

        Vector getVelocity(long time) {
            if (time > this.time) {
                return null;
            } else if (time == this.time) {
                return velocity;
            } else {
                Data prev = null, next = null;
                for (Data data : history) {
                    if (data.time < time) {
                        if (prev == null || prev.time < data.time) {
                            prev = data;
                        }
                    } else if (data.time == time) {
                        return data.velocity;
                    } else {
                        if (next == null || next.time > data.time) {
                            next = data;
                        }
                    }
                }
                if (prev == null && next == null) {
                    return null;
                } else if (prev == null) {
                    return next.velocity;
                } else if (next == null) {
                    return prev.velocity;
                } else {
                    // use linear interpolation, we should be able to do better by using the velocity
                    Vector v1 = prev.velocity.scale(((double) time - prev.time) / (next.time - prev.time));
                    Vector v2 = next.velocity.scale(((double) next.time - time) / (next.time - prev.time));
                    return v1.add(v2);
                }
            }
        }

        public boolean isAlive(long time) {
            return death == 0 || time < death;
        }

        Stream<Robot> others() {
            return robots.otherRobots(this);
        }

        KDTree<MeleeScan> getMoveTree(String name) {
            return LaserToaster.getMoveTree(this.name, name);
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

        public double[] targetDescriptor(Wave wave) {
            Point fireLocation = wave.firer.getLocation(wave.timeMin);
            Point location = this.getLocation(wave.timeMin);
            Vector velocity = this.getVelocity(wave.timeMin);
            if (location == null || velocity == null) {
                return new double[DESCRIPTOR_SIZE];
            }
            Vector velocityLast1 = this.getVelocity(wave.timeMin - 1);
            Point locationLast10 = getLocation(wave.timeMin - 10);
            double botsAlive = robots.robots().filter(r -> r.isAlive(wave.timeMin)).count();
            Vector sub = location.sub(fireLocation);
            double latVel = velocity.m * Math.sin(velocity.d - sub.d);
            double advVel = velocity.m * Math.cos(velocity.d - sub.d);
            double distToE = sub.m;
            double accel = Math.abs(velocity.m) - Math.abs(velocityLast1.m);
            double distLast10 = locationLast10 != null ? location.distance(locationLast10) : 0;
            double distToNearest = robots.robots().filter(r -> r != this && r.isAlive(wave.timeMin))
                    .map(r -> r.getLocation(wave.timeMin))
                    .filter(Objects::nonNull)
                    .mapToDouble(location::distance)
                    .min().getAsDouble();
            double distToWall = Math.min(
                    Math.min(location.x - 18, location.y - 18),
                    Math.min(MAX_X - 18 - location.x, MAX_Y - 18 - location.y));
            double distToCorner = Stream.of(Point.fromXY(0, 0),
                    Point.fromXY(0, MAX_Y),
                    Point.fromXY(MAX_X, 0),
                    Point.fromXY(MAX_X, MAX_Y)).mapToDouble(location::distance).min().getAsDouble();
            int timeSinceReverse = 1;
            while (timeSinceReverse < 30) {
                Vector v = getVelocity(time - timeSinceReverse);
                if (v != null && Math.signum(v.m) * Math.signum(velocity.m) > 0.0) {
                    timeSinceReverse++;
                } else {
                    break;
                }
            }
            return new double[]{
                    10.0 * (Math.abs(latVel) / Rules.MAX_VELOCITY),
                    4.0 * (1.0 / botsAlive),
                    3.0 * ((accel + 2.0) / 3.0),
                    2.0 * ((advVel + 8.0 / 16.0)),
                    2.0 * (distLast10 / (Rules.MAX_VELOCITY * 10)),
                    2.0 * (distToNearest / 1200.0),
                    2.0 * (distToWall / 500.0),
                    2.0 * (distToCorner / 700.0),
                    2.0 * (1.0 / (1.0 + 2.0 * timeSinceReverse / (distToNearest / 14))),
                    1.0 * (distToE / 1200.0)
            };
        }
    }

    class SelfRobot extends Robot {
        double bodyHeading;
        double gunHeading;
        double gunHeat;
        double radarHeading;

        public SelfRobot(Robots robots, String name) {
            super(robots, name, true);
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

    class Robots {
        private final AdvancedRobot actor;
        private final Map<String, Robot> robots = new HashMap<>();
        private final SelfRobot self;

        public Robots(AdvancedRobot actor) {
            this.actor = actor;
            this.self = new SelfRobot(this, actor.getName());
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
            // Hit by bullet
            events.stream()
                    .filter(HitByBulletEvent.class::isInstance)
                    .map(HitByBulletEvent.class::cast)
                    .forEach(hbbe -> {
//						robots.computeIfAbsent(hbbe.getName(), this::newRobot)
//								.energy += Rules.getBulletHitBonus(hbbe.getPower());
                    });
            // Scanned robots updates
            events.stream()
                    .filter(ScannedRobotEvent.class::isInstance)
                    .map(ScannedRobotEvent.class::cast)
                    .forEach(sre -> {
                        robots.computeIfAbsent(sre.getName(), this::newRobot).update(
                                sre.getName(),
                                Point.fromXY(statusEvent.getStatus().getX(), statusEvent.getStatus().getY())
                                        .add(Vector.fromDM(statusEvent.getStatus().getHeadingRadians() + sre.getBearingRadians(), sre.getDistance())),
                                Vector.fromDM(sre.getHeadingRadians(), sre.getVelocity()),
                                sre.getEnergy(),
                                sre.getTime() - 1);
                    });
            // Interpolate
            interpolate();
            // Flag waves to update
            Stream.concat(events.stream()
                                .filter(BulletHitBulletEvent.class::isInstance)
                                .map(BulletHitBulletEvent.class::cast)
                                .map(BulletHitBulletEvent::getHitBullet),
                          events.stream()
                                .filter(HitByBulletEvent.class::isInstance)
                                .map(HitByBulletEvent.class::cast)
                                .map(HitByBulletEvent::getBullet))
                    .map(Bullet::getName)
                    .map(robots::get)
                    .flatMap(r -> r.waves.stream())
                    .forEach(w -> w.needRecalc = true);
            // Create waves
            updateWaves(events);
            // Robot deaths
            events.stream()
                    .filter(RobotDeathEvent.class::isInstance)
                    .map(RobotDeathEvent.class::cast)
                    .forEach(de -> robots.computeIfAbsent(de.getName(), this::newRobot).death = de.getTime());
        }

        private void interpolate() {
            aliveEnemies().forEach(Robot::interpolate);
        }

        private void updateWaves(List<Event> events) {
            events.stream()
                    .filter(BulletMissedEvent.class::isInstance)
                    .map(BulletMissedEvent.class::cast)
                    .forEach(bhbe -> {
                        Bullet hitBullet = bhbe.getBullet();
                        Point l = Point.fromXY(hitBullet.getX(), hitBullet.getY());
                        List<Wave> waves = self.waves.stream()
                                .filter(w -> isNear(w.energy, hitBullet.getPower()))
                                .filter(w -> {
                                    for (long t = w.timeMin; t <= w.timeMax; t++) {
                                        Point org = l.add(Vector.fromDM(hitBullet.getHeadingRadians() + Math.PI, hitBullet.getVelocity()),
                                                bhbe.getTime() - t);
                                        Point rl = self.getLocation(t);
                                        if (org.distance(rl) < 20.0) {
                                            return true;
                                        }
                                    }
                                    return false;
                                })
                                .collect(Collectors.toList());
                        if (waves.isEmpty()) {
                            printf("Unable to find matching wave for bullet missed event");
                        } else if (waves.size() > 1) {
                            printf("Multiple wave candidates for bullet missed event");
                        } else {
                            Wave w = waves.get(0);
                            self.waves.remove(w);
                            self.historicWaves.add(w);
                        }
                    });
            events.stream()
                    .filter(BulletHitBulletEvent.class::isInstance)
                    .map(BulletHitBulletEvent.class::cast)
                    .forEach(bhbe -> {
                        Bullet hitBullet = bhbe.getHitBullet();
                        String enemyName = hitBullet.getName();
                        Robot r = robots.get(enemyName);
                        if (r != null) {
                            Point l = Point.fromXY(hitBullet.getX(), hitBullet.getY());
                            List<Wave> waves = r.waves.stream()
                                    .filter(w -> isNear(w.energy, hitBullet.getPower()))
                                    .filter(w -> {
                                        for (long t = w.timeMin; t <= w.timeMax; t++) {
                                            Point org = l.add(Vector.fromDM(hitBullet.getHeadingRadians() + Math.PI, hitBullet.getVelocity()),
                                                    bhbe.getTime() - t);
                                            Point rl = r.getLocation(t);
                                            if (org.distance(rl) < 20.0) {
                                                return true;
                                            }
                                        }
                                        return false;
                                    })
                                    .collect(Collectors.toList());
                            if (waves.isEmpty()) {
                                printf("Unable to find matching wave for bullet hit bullet event");
                            } else if (waves.size() > 1) {
                                printf("Multiple wave candidates for bullet hit bullet event");
                            } else {
                                Wave w = waves.get(0);
                                r.waves.remove(w);
                                r.historicWaves.add(w);
                            }
                        }
                    });
            robots().filter(Robot::isAlive).forEach(Robot::updateWaves);
            robots().filter(Robot::isAlive).forEach(Robot::createNewWaves);
            robots().filter(Robot::isAlive).forEach(Robot::dropOldWaves);
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

        public Stream<Robot> otherRobots(Robot robot) {
            return robots().filter(r -> r != robot);
        }

        public List<Robot> aliveEnemies() {
            return robots()
                    .filter(Robot::isAlive)
                    .filter(Robot::isEnemy)
                    .collect(Collectors.toList());
        }

    }

    interface Radar {
        void run(List<Event> events);

        void onPaint(Graphics2D g);
    }

    static abstract class BaseRadar implements Radar {
        final LaserToaster actor;
        final Robots robots;
        boolean paint = true;
        double prevHeading = Double.NaN;
        double pprevHeading = Double.NaN;
        double ppprevHeading = Double.NaN;

        public BaseRadar(LaserToaster actor, Robots robots) {
            this.actor = actor;
            this.robots = robots;
        }

        @Override
        public void onPaint(Graphics2D g) {
            if (!paint) {
                return;
            }
            if (Double.isNaN(prevHeading)) {
                prevHeading = actor.getRadarHeadingRadians();
                return;
            }
            if (Double.isNaN(pprevHeading)) {
                pprevHeading = prevHeading;
                return;
            }
            if (Double.isNaN(ppprevHeading)) {
                ppprevHeading = pprevHeading;
                return;
            }
            Stroke prevStroke = g.getStroke();
            final int nbIter = 32;
            double x = actor.getX();
            double y = actor.getY();
            double a0 = Math.toDegrees(ppprevHeading) + 270;
            double a1 = Math.toDegrees(pprevHeading) + 270;
            if (a1 - a0 > 180) {
                a0 += 360;
            } else if (a0 - a1 > 180) {
                a1 += 360;
            }
            double e = (a1 - a0) / nbIter;
            for (int i = 0; i < nbIter; i++) {
                g.setPaint(new Color(0.0f, 1.0f, 0.0f, 0.00f + (0.15f * i) / (nbIter - 1)));
                double s = a0 + i * (a1 - a0) / nbIter;
                g.fill(new Arc2D.Double(x - 1200, y - 1200, 2400, 2400, s, e, Arc2D.PIE));
            }

            a0 = Math.toDegrees(pprevHeading) + 270;
            a1 = Math.toDegrees(prevHeading) + 270;
            if (a1 - a0 > 180) {
                a0 += 360;
            } else if (a0 - a1 > 180) {
                a1 += 360;
            }
            e = (a1 - a0) / nbIter;
            for (int i = 0; i < nbIter; i++) {
                g.setPaint(new Color(0.0f, 1.0f, 0.0f, 0.15f + (0.20f * i) / (nbIter - 1)));
                double s = a0 + i * (a1 - a0) / nbIter;
                g.fill(new Arc2D.Double(x - 1200, y - 1200, 2400, 2400, s, e, Arc2D.PIE));
            }
            g.setPaint(new Color(0.0f, 1.0f, 0.0f, 0.5f));
            g.setStroke(new BasicStroke(2.0f));
            g.draw(new Line2D.Double(x, y, x + 1200 * Math.cos(-prevHeading + Math.PI / 2), y + 1200 * Math.sin(-prevHeading + Math.PI / 2)));
            ppprevHeading = pprevHeading;
            pprevHeading = prevHeading;
            prevHeading = actor.getRadarHeadingRadians();
            g.setStroke(new BasicStroke(2.0f));
            for (Robot r : robots.aliveEnemies()) {
                if (r.time == robots.self.time - 1) {
                    g.setPaint(new Color(0.0f, 1.0f, 0.0f, 0.5f));
                } else {
                    g.setPaint(new Color(0.6f, 0.6f, 0.6f, 0.5f));
                }
                g.draw(new Rectangle2D.Double(r.location.x - 18, r.location.y - 18, 36, 36));
            }
            g.setStroke(prevStroke);
        }
    }

    class MeleeRadar extends BaseRadar {
        private int direction;
        Robot oldest;
        double radar;
        double target;
        double bearing;

        public MeleeRadar(LaserToaster actor, Robots robots) {
            super(actor, robots);
        }

        public void run(List<Event> events) {
            // Enable / disable radar painting
            events.stream()
                    .filter(KeyTypedEvent.class::isInstance)
                    .map(KeyTypedEvent.class::cast)
                    .filter(kte -> kte.getSourceEvent().getKeyChar() == 'r')
                    .forEach(kte -> paint = !paint);
            // TODO: the radar does not support not finding an enemy at the beginning of the game
            if (!robots.haveFoundAll()) {
                if (direction == 0) {
                    printf("Initial radar spin");
                    direction = computeInitialDirection();
                }
                actor.setTurnGunRightRadians(direction * Rules.MAX_TURN_RATE_RADIANS);
                actor.setTurnRightRadians(direction * (Rules.GUN_TURN_RATE_RADIANS + Rules.MAX_TURN_RATE_RADIANS));
                actor.setTurnRadarRightRadians(direction * (Rules.RADAR_TURN_RATE_RADIANS + Rules.GUN_TURN_RATE_RADIANS + Rules.MAX_TURN_RATE_RADIANS));
                return;
            } else if (direction != 0) {
                printf("Radar melee mode");
                direction = 0;
            }
            radar = actor.getRadarHeadingRadians();
            List<Robot> enemies = robots.aliveEnemies();
            long oldestTick = enemies.stream().mapToLong(Robot::getTime).min().orElse(0);
            if (robots.self.time - oldestTick > 8) {
                if (Math.abs(actor.getRadarTurnRemainingRadians()) < 100.0) {
                    printf("Sweeping");
                }
                actor.setTurnRadarRightRadians(Double.POSITIVE_INFINITY);
                // check for missed death events ?
                // TODO: this is not true in big battlefields where robots could be far away
                List<Robot> deaths = enemies.stream().filter(r -> robots.self.time - r.time > 8).collect(Collectors.toList());
                if (deaths.size() + actor.getOthers() == enemies.size()) {
                    deaths.forEach(r -> r.death = robots.self.time);
                }
                return;
            } else if (Math.abs(actor.getRadarTurnRemainingRadians()) > 100.0) {
                printf("Stopped sweeping");
            }
            double min = Math.PI;
            double max = -Math.PI;
            double minesc = Math.PI;
            double maxesc = -Math.PI;
            int oldestMinHeat = 32;
            Robot robotMinHeat = null;
            for (Robot r : enemies) {
                Vector d = robots.self.location.sub(r.location);
                double b = Utils.normalRelativeAngle(d.d - radar);
                if (r.getTime() == oldestTick) {
                    double escape = Math.asin(Rules.MAX_VELOCITY * (robots.self.time - r.time) / d.m);
                    if (Double.isNaN(escape)) {
                        escape = 2 * Math.PI;
                    }
                    min = Math.min(min, b);
                    max = Math.max(max, b);
                    minesc = Math.min(minesc, b - escape);
                    maxesc = Math.max(maxesc, b + escape);
                    double heat = r.heat - GUN_COOLING_RATE * (robots.self.time - r.time);
                    int h = (int) Math.ceil((heat - NEAR_DELTA) / GUN_COOLING_RATE);
                    oldestMinHeat = Math.min(h, oldestMinHeat);
                } else {
                    if (robotMinHeat == null) {
                        robotMinHeat = r;
                    } else {
                        double heat = r.heat - GUN_COOLING_RATE * (robots.self.time - r.time);
                        double minheat = robotMinHeat.heat - GUN_COOLING_RATE * (robots.self.time - robotMinHeat.time);
                        if (heat < minheat) {
                            robotMinHeat = r;
                        }
                    }
                }
            }
            // min and max on same side
            double turn;
            if (min * max > 0.0) {
                turn = max > 0.0 ? maxesc : minesc;
            } else if (Math.abs(min) < Math.abs(max)) {
                turn = minesc;
            } else {
                turn = maxesc;
            }
            // check if we should go to the robot that will fire soon
            // TODO: finish locking implementation, the decision to lock should not belong to the radar
            if (robotMinHeat != null) {
                Vector d = robots.self.location.sub(robotMinHeat.location);
                double b = Utils.normalRelativeAngle(d.d - radar);
                double escape = Math.asin(Rules.MAX_VELOCITY * (robots.self.time - robotMinHeat.time) / d.m);
                if (Double.isNaN(escape)) {
                    escape = 2 * Math.PI;
                }
                double wturn = b > 0.0 ? b + escape : b - escape;
                double heat = robotMinHeat.heat - GUN_COOLING_RATE * (robots.self.time - robotMinHeat.time);
                int h = (int) Math.ceil((heat - NEAR_DELTA) / GUN_COOLING_RATE);
                if ((h == 1 || h == 2) && wturn * turn < 0) {
                    Robot theRobotMinHeat = robotMinHeat;
                    boolean ok = enemies.stream()
                            .filter(r -> r != theRobotMinHeat)
                            .allMatch(r -> {
                                Vector dr = robots.self.location.sub(r.location);
                                double br = Utils.normalRelativeAngle(dr.d - (radar + wturn));
                                double er = Math.asin(Rules.MAX_VELOCITY * (robots.self.time - r.time) / d.m);
                                double htr = Math.max(0.0, r.heat - GUN_COOLING_RATE * (robots.self.time - r.time));
                                int hr = (int) Math.ceil((htr - NEAR_DELTA) / GUN_COOLING_RATE);
                                return hr >= Math.abs(br > 0.0 ? br + er : br - er) / Rules.RADAR_TURN_RATE_RADIANS;
                            });
                    if (ok) {
//						turn = wturn;
                    }
                }
            }
//			printf("Turning radar: %6.1f from %6.1f to %6.1f / %6.1f%n", Math.toDegrees(turn), Math.toDegrees(radar), Math.toDegrees(radar + min), Math.toDegrees(radar + max));
            actor.setTurnRadarRightRadians(turn);
        }

        private int computeInitialDirection() {
            Point center = Point.fromXY(actor.getBattleFieldWidth() / 2, actor.getBattleFieldHeight() / 2);
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
            return "MeleeRadar{" +
                    "oldest=" + (oldest != null ? oldest.name : "n/a") +
                    ", radar=" + radar +
                    ", target=" + target +
                    ", bearing=" + bearing +
                    '}';
        }
    }

    interface Targeting {
        void init(Robots robots, Robot enemy);

        default void tick() { }

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
                    maxX = (int) MAX_X - WALL_MIN_DIST,
                    maxY = (int) MAX_Y - WALL_MIN_DIST;
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

    static class TreeTargeting implements Targeting {

        static class GunScan {

            static final int DIMENSION = 7;

            long time;
            Point selfLoc;
            double enemyHeading;
            double bearing;
            double bearingRadians;
            double normalizedDistance;
            double distance;
            double distanceDelta;
            double lateralVelocity;
            double advancingVelocity;
            double acceleration;
            double velocity;
            double sinceVelocityChange;
            double wallTriesForward;
            double wallTriesBack;
            double gunHeat;
            double direction;
            double bulletVelocity;
            boolean isRealBullet;
            double maxAngle;
            boolean set = false;
            boolean deltaSet = false;

            public double getDistance(long time) {
                return (double) (time - this.time) * bulletVelocity;
            }

            double[] location() {
                return new double[] { lateralVelocity, advancingVelocity, acceleration, sinceVelocityChange,
                        normalizedDistance, wallTriesForward, wallTriesBack};
            }

            public void setBulletVelocity(double shotPower) {
                bulletVelocity = 20d - 3d * shotPower;
                maxAngle = Math.asin(8d / bulletVelocity) * direction;
            }

            public boolean setBearing(Point loc) {
                boolean val = set;
                if (!set) {
                    register(loc);
                }
                if (!deltaSet) {
                    distanceDelta = selfLoc.distance(loc) - distance;
                    deltaSet = true;
                }
                return val;
            }

            public void registerHit(Point loc) {
                register(loc);
            }

            private void register(Point loc) {
                bearingRadians = Utils.normalRelativeAngle(loc.sub(selfLoc).d - enemyHeading);
                bearing = (bearingRadians / maxAngle) * 100d;
                set = true;
            }

        }

        static final Map<String, KDTree<GunScan>> TREES = new HashMap<>();
        static final double BAND_WIDTH = 6.0d;
        static final Rect WALLS = new Rect(10, 10, MAX_X - 20, MAX_Y - 20);

        Robots robots;
        Robot enemy;
        GunScan scan;
        double _lastVelocity;
        double _lastVelocityChange;

        @Override
        public void init(Robots robots, Robot enemy) {
            this.robots = robots;
            this.enemy = enemy;
        }

        @Override
        public void tick() {
            if (scan == null || scan.time < enemy.time) {
                Vector rToE = enemy.location.sub(robots.self.location);
                double enemyHeading = enemy.velocity.d;
                double relativeHeading = rToE.d - enemyHeading;
                double distance = rToE.m;
                long time = robots.self.time;

                //calculate indexes=====================
                double velocity = enemy.velocity.m;
                double absVelocity = Math.abs(velocity);
                double lateralVelocity = velocity * Math.sin(relativeHeading);
                double advancingVelocity = -Math.cos(relativeHeading) * velocity;
                double direction = lateralVelocity < 0 ? -1 : 1;

                double acceleration = 0;
                if (_lastVelocity != Double.MAX_VALUE) {
                    if (_lastVelocity * velocity >= 0.0) {
                        acceleration = Math.abs(velocity) - Math.abs(_lastVelocity);
                    } else {
                        acceleration = Math.abs(velocity - _lastVelocity);
                    }
                } else {
                    acceleration = velocity;
                }
                acceleration = Math.abs(Math.max(Math.min(acceleration, 2d), -2d));

                _lastVelocityChange++;
                if (Math.abs(_lastVelocity - velocity) > 0.1) {
                    _lastVelocityChange = 0;
                }
                double velocityChangeValue = Math.min(_lastVelocityChange, 35d);

                // wall distance forward
                double wallTries = getWallTries(enemyHeading, direction, distance);
                double wallTriesBack = getWallTries(enemyHeading, -direction, distance);

                lateralVelocity = Math.abs(lateralVelocity);

                scan = new GunScan();
                scan.time = time - 1;
                scan.lateralVelocity = lateralVelocity / 8d;
                scan.advancingVelocity = advancingVelocity / 32d;
                scan.wallTriesForward = wallTries / 20d;
                scan.wallTriesBack = wallTriesBack / 20d;
                scan.normalizedDistance = distance / 800d;
                scan.distance = distance;
                scan.velocity = absVelocity / 8d;
                scan.acceleration = acceleration / 2d;
                scan.sinceVelocityChange = velocityChangeValue / 35d;
                scan.gunHeat = enemy.heat / 1.6d;
                scan.direction = direction;
                scan.enemyHeading = enemyHeading;
                scan.selfLoc = robots.self.location;
            }
        }

        @Override
        public double computeAngle(double firePower) {
            List<KDTree.SearchResult<GunScan>> cluster = getTree().nearestNeighbours(scan.location(), 50);
            if (cluster.size() > 0) {
                GunScan best = cluster.stream()
                        .map(KDTree.SearchResult::getPayload)
                        .max(Comparator.comparingDouble(s1 -> cluster.stream()
                                .map(KDTree.SearchResult::getPayload)
                                .mapToDouble(s2 -> Math.exp(-0.5d * sqr((s1.bearing - s2.bearing) / BAND_WIDTH)))
                                .sum()))
                        .get();
                double theBearing = (best.bearingRadians * scan.maxAngle) / best.maxAngle;
                double projectedDistance = scan.distance + best.distanceDelta;
                Point projected = robots.self.location.add(Vector.fromDM(theBearing, projectedDistance));
                if (WALLS.contains(projected)) {
                    return theBearing;
                }
            }
            return Double.MAX_VALUE;
        }

        private double getWallTries(double heading, double dir, double distance) {
            double wallIncrement = 0.0407d * dir;
            double eHeading = heading;
            Point next;
            double wallTries = -1;
            do {
                eHeading += wallIncrement;
                next = robots.self.location.add(Vector.fromDM(eHeading, distance));
                wallTries++;
            } while (WALLS.contains(next) && wallTries < 20);
            return wallTries;
        }

        private KDTree<GunScan> getTree() {
            return TREES.computeIfAbsent(enemy.name, s -> new KDTree.WeightedManhattan<>(GunScan.DIMENSION));
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

    /**
     * Small class to compute an average on a rolling window of values.
     */
    public static class Averager {

        private final int size;
        private final double[] values;
        private int index;
        private double total;

        public Averager(int size) {
            this.size = size;
            this.values = new double[size];
        }

        public void addValue(double value) {
            int m = index % size;
            total += value - values[m];
            values[m] = value;
            index++;
        }

        public double getAverage() {
            return total / Math.min(index, size);
        }
    }

    static class VirtualGun {
        static final Map<String, Map<String, Averager>> HITS = new HashMap<>();

        final Targeting targeting;
        final Robots robots;
        final Robot enemy;
        final List<VirtualBullet> bullets = new ArrayList<>();

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
            return getAverager().getAverage();
        }

        private Averager getAverager() {
            return HITS.computeIfAbsent(enemy.name, n -> new HashMap<>())
                    .computeIfAbsent(targeting.getClass().getSimpleName(), n -> new Averager(64));
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
                        getAverager().addValue(1.0);
                        it.remove();
                    } else if (bullet.testMiss(t)) {
                        getAverager().addValue(0.0);
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
                double walls = (MAX_X + MAX_Y) / 2.0;
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
            double wallDist = MAX_Y - robots.self.location.y - WALL_MIN_DIST;
            if (a < robots.self.location.angleTo(Point.fromXY(MAX_X, MAX_Y))) {
            } else if (a < robots.self.location.angleTo(Point.fromXY(MAX_X, 0.0))) {
                a -= 0.5 * Math.PI;
                wallDist = MAX_X - robots.self.location.x - WALL_MIN_DIST;
            } else if (a < robots.self.location.angleTo(Point.fromXY(0.0, 0.0))) {
                a -= 1.0 * Math.PI;
                wallDist = robots.self.location.y - WALL_MIN_DIST;
            } else if (a < robots.self.location.angleTo(Point.fromXY(0.0, MAX_Y))) {
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
            double dist = robot.location.distance(robots.self.location) / Math.sqrt((MAX_Y - WALL_MIN_DIST * 2.0) * (MAX_X - WALL_MIN_DIST * 2.0));
            double wall = (Math.min(robot.location.x, MAX_X - robot.location.x) - WALL_MIN_DIST) / (MAX_X / 2.0 - WALL_MIN_DIST)
                    * (Math.min(robot.location.y, MAX_Y - robot.location.y) - WALL_MIN_DIST) / (MAX_Y / 2.0 - WALL_MIN_DIST);
            double nrj = robot.energy / 100.0;
            double gun = 1.0 - robot.getBestGun().getHitRate();
            return Math.floor(Math.sqrt(dist) * 4) * 1 + wall * wall * 0 + Math.floor(Math.sqrt(nrj) * 4) * 1 + Math.floor(Math.sqrt(gun) * 10) * 1;
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

    static class MeleeStrategy {

        private final AdvancedRobot actor;
        private final Robots robots;
        List<Movement> movements;
        Point next;
        Gun gun;

        boolean paintMovement = true;
        boolean paintEnemyRisk = true; // E
        boolean paintWaveRisk = true;  // W

        public MeleeStrategy(AdvancedRobot actor, Robots robots) {
            this.actor = actor;
            this.robots = robots;
            this.gun = new Gun(actor, robots);
        }

        public void run(Collection<Event> events) {
            events.stream()
                    .filter(KeyPressedEvent.class::isInstance)
                    .map(KeyPressedEvent.class::cast)
                    .forEach(kpe -> {
                        switch (kpe.getSourceEvent().getKeyChar()) {
                            case 'e': paintEnemyRisk = !paintEnemyRisk; break;
                            case 'w': paintWaveRisk = !paintWaveRisk; break;
                            case 'm': paintMovement = !paintMovement; break;
                        }
                    });
            // choose target
            List<Robot> enemies = this.robots.aliveEnemies();

            gun.run();

            // choose next point if needed
            movements = generatePoints()
                    .filter(BATTLEFIELD::contains)
                    .sorted(Comparator.comparing(p -> this.robots.self.location.sub(p).d))
                    .map(this::move)
                    .collect(Collectors.toList());

            normalizeMedian(movements, m -> m.enemyRisk, (m, r) -> m.enemyRisk = r);
            normalizeMedian(movements, m -> m.waveRisk, (m, r) -> m.waveRisk = r);
            double we = 1; // * limit(1e-5, enemies.size() - 1, 5);
            double ww = 2; //enemies.size() * 2 + 1;
            double wn = 0.1;
            if (next != null) {
                movements.forEach(m -> {
                    double nr = sqr(next.distance(m.target) / 600.0);
                    m.risk = m.enemyRisk * we + m.waveRisk * ww + nr * wn;
                });
            } else {
                movements.forEach(m -> m.risk = m.enemyRisk * we + m.waveRisk * ww);
            }
            normalizeMax(movements, m -> m.risk, (m, r) -> m.risk = r);

            movements.sort(Comparator.comparingDouble(m -> m.risk));
            next = movements.stream()
                    .min(Comparator.comparingDouble(m -> m.risk))
                    .map(m -> m.target)
                    .get();

            goTo(next);
        }

        private Movement move(Point target) {
            Movement movement = new Movement();
            movement.target = target;
            movement.data = MovementInterpolator.simulate(
                    new Data(robots.self.time, robots.self.location, robots.self.velocity),
                    (d, cmd) -> goTo(d.location, target, d.velocity.d, cmd));
            movement.enemyRisk = evalEnemyRisk(movement);
            movement.waveRisk = evalWaveRisk(movement);
            return movement;
        }

        private boolean hasReached(Point p) {
            return robots.self.location.sub(p).m <= 18.0;
        }

        static class HitData {
            final Wave wave;
            final Data data;
            final long fireTime;
            final Point fireLocation;

            public HitData(Wave wave, Data hitPoint, long fireTime, Point fireLocation) {
                this.wave = wave;
                this.data = hitPoint;
                this.fireTime = fireTime;
                this.fireLocation = fireLocation;
            }

            public double danger() {
                double bearing = Utils.normalAbsoluteAngle(absoluteBearing(fireLocation, data.location));
                double botWidth = 40 / fireLocation.distance(data.location);
                double scale = 180 / Math.PI;
                double a1 = Utils.normalAbsoluteAngle(bearing - botWidth * 0.5);
                double a2 = Utils.normalAbsoluteAngle(bearing + botWidth * 0.5);
                double[] bins = wave.calcDangers(data.location);
                double waveDanger = botWidth * averageDanger((int) (scale * a1), (int) (scale * a2), bins, wave.botShadowBins);
                double tth = data.location.distance(fireLocation) / wave.bulletSpeed - (data.time - wave.timeMin);
                double waveWeight = Rules.getBulletDamage(wave.energy) * Math.pow(0.8, tth);
                return waveWeight * waveDanger;
            }
        }

        // evaluate the risk of a given target point
        private double evalWaveRisk(Movement movement) {
            // Compute hit points
            movement.waveHitPoints = robots.aliveEnemies().stream()
                    // get all waves
                    .flatMap(r -> r.waves.stream())
                    // find hit point
                    .map(w -> {
                        Map<Long, Point> locs = LongStream.range(w.timeMin, w.timeMax + 1)
                                .boxed()
                                .collect(Collectors.toMap(t -> t, w.firer::getLocation));
                        return movement.data.stream()
                                .flatMap(d -> locs.entrySet().stream().map(e -> new HitData(w, d, e.getKey(), e.getValue())))
                                .filter(hd -> Math.abs(hd.data.location.distance(hd.fireLocation) - w.bulletSpeed * (hd.data.time - hd.fireTime)) < 8)
                                .min(Comparator.comparingDouble(hd -> hd.data.time));
                    })
                    .flatMap(o -> o.map(Stream::of).orElseGet(Stream::empty))
                    .collect(Collectors.toList());
            return movement.waveHitPoints.stream()
                    // compute danger for this hit point
                    .mapToDouble(HitData::danger)
                    // sum for each wave
                    .sum();
			/*
			double risk = 0.0;
			for (Robot r : robots.aliveEnemies()) {
				for (Wave w : r.waves) {
					Map<Long, Point> locs = LongStream.range(w.timeMin, w.timeMax + 1)
							.boxed()
							.collect(Collectors.toMap(t -> t, w.firer::getLocation));
					Optional<HitData> hitPointOpt = movement.data.stream()
							.flatMap(d -> locs.entrySet().stream().map(e -> new HitData(d, e.getKey(), e.getValue())))
							.filter(hd -> hd.data.location.distance(hd.fireLocation) < w.bulletSpeed * (hd.data.time - hd.fireTime))
							.sorted(Comparator.comparingLong(hd -> hd.data.time))
							.findFirst();
					if (hitPointOpt.isPresent()) {
						Point fireLocation = hitPointOpt.get().fireLocation;
						Point hitPoint = hitPointOpt.get().data.location;
						long time = hitPointOpt.get().data.time;
						double bearing = Utils.normalAbsoluteAngle(absoluteBearing(fireLocation, hitPoint));
						double botWidth = 40 / fireLocation.distance(hitPoint);
						double scale = 180 / Math.PI;
						double a1 = Utils.normalAbsoluteAngle(bearing - botWidth * 0.5);
						double a2 = Utils.normalAbsoluteAngle(bearing + botWidth * 0.5);
						double[] bins = w.calcDangers(hitPoint);
						double waveDanger = botWidth * averageDanger((int) (scale * a1), (int) (scale * a2), bins, w.botShadowBins);

						double tth = hitPoint.distance(fireLocation) / w.bulletSpeed - (time - w.timeMin);
						double waveWeight = Rules.getBulletDamage(w.energy) * Math.pow(0.8, tth);

						movement.hitPoints.add(hitPoint);
						risk += waveWeight * waveDanger;
					}
				}
			}
			return risk;
		    */
        }

        static void smoothAround(double[] bins, int index, int width, double weight) {
            int minIndex = (index - 2 * width + 2 * bins.length) % bins.length;
            int maxIndex = (index + 2 * width) % bins.length;
            double invWidth = 1.0 / width;
            if (minIndex > index) {
                for (int i = minIndex; i < bins.length; i++)
                    bins[i] += weight / (sqr(i - bins.length - index) * invWidth + 1);
                for (int i = 0; i < index; i++)
                    bins[i] += weight / (sqr(i - index) * invWidth + 1);
            } else {
                for (int i = minIndex; i < index; i++)
                    bins[i] += weight / (sqr(i - index) * invWidth + 1);
            }
            if (maxIndex < index) {
                for (int i = index; i < bins.length; i++)
                    bins[i] += weight / (sqr(i - index) * invWidth + 1);
                for (int i = 0; i <= maxIndex; i++)
                    bins[i] += weight / (sqr(i + bins.length - index) * invWidth + 1);
            } else {
                for (int i = index; i <= maxIndex; i++)
                    bins[i] += weight / (sqr(i - index) * invWidth + 1);
            }
        }

        static double averageDanger(int i1, int i2, double[] bins, double[] enableBins) {
            double d = 0;
            if (i1 < i2) {
                for (int i = i1; i <= i2; i++)
                    d += bins[i] * enableBins[i];
                d /= i2 - i1 + 1;
            } else {
                for (int i = i1; i < bins.length; i++)
                    d += bins[i] * enableBins[i];
                for (int i = 0; i <= i2; i++)
                    d += bins[i] * enableBins[i];
                d /= bins.length - i1 + i2 + 1;
            }
            return d;
        }


        private double evalEnemyRisk(Movement movement) {
            return movement.data.stream()
                    .mapToDouble(d -> this.robots.aliveEnemies().stream()
                                .mapToDouble(r -> r.energy / (1e-20 + r.location.distance(d.location)))
                                .sum())
                    .average()
                    .orElse(Double.POSITIVE_INFINITY);
            /*
            List<Robot> enemies = this.robots.aliveEnemies();
            for (Robot r : enemies) {
                double dist = Math.max(0.0, movement.target.distance(r.location) - 30.0);
                double closest = 1;
                double minEDist = Double.POSITIVE_INFINITY;
                for (Robot e : enemies) {
                    if (e != r) {
                        double edist = e.location.distance(r.location);
                        if (edist < minEDist) {
                            minEDist = edist;
                        }
                        if (dist < edist * 1.2) {
                            closest++;
                        }
                    }
                }
                closest = limit(1, closest - enemies.size() + 1, 3);

                double minDist = movement.data.stream().mapToDouble(p -> r.location.distance(p.location)).min().getAsDouble();
                if (minDist < 1.3 * minEDist) {
                    double anglediff = absoluteBearing(robots.self.location, movement.target) - absoluteBearing(r.location, robots.self.location);
                    eval += r.energy / sqr(dist) * closest * (1 + Math.abs(Math.cos(anglediff)));
                } else {
                    eval += r.energy / sqr(dist) * closest;
                }
            }
            return eval;
            */
        }

        // generate a stream of points
        private Stream<Point> generatePoints() {
            int nbPoints = 16;
            double closestEnemy = robots.aliveEnemies().stream().map(r -> r.location.distance(robots.self.location))
                    .min(Comparator.naturalOrder()).orElse(100.0);
            double mag1 = limit(48, closestEnemy * 8 / 14, 160);
            double mag2 = limit(148, closestEnemy * 8 / 11, 300);
            return Stream.concat(
                    // Close points
                    IntStream.range(0, nbPoints)
                            .mapToDouble(i -> (i * 2 * Math.PI) / nbPoints)
                            .boxed()
                            .map(a -> robots.self.location.add(Vector.fromDM(a, mag1))),
                    // Further points
                    IntStream.range(0, nbPoints)
                            .mapToDouble(i -> ((i + 0.5) * 2 * Math.PI) / nbPoints)
                            .boxed()
                            .map(a -> robots.self.location.add(Vector.fromDM(a, mag2))));
        }

        private void goTo(Point p) {
            MovementInterpolator.Command cmd = new MovementInterpolator.Command();
            goTo(robots.self.location, p, robots.self.bodyHeading, cmd);
            actor.setTurnRightRadians(cmd.bodyTurnRemaining);
            actor.setAhead(cmd.distanceRemaining);
        }

        static boolean goTo(Point location, Point target, double heading, MovementInterpolator.Command cmd) {
            double distance = location.distance(target);
            double dir = 1;
            double angle = Utils.normalRelativeAngle(absoluteBearing(location, target) - heading);
            if (Math.abs(distance) < 1) {
                return false;
            }
            if (Math.abs(angle) > Math.PI / 2) {
                dir = -1;
                if (angle > 0) {
                    angle -= Math.PI;
                } else {
                    angle += Math.PI;
                }
            }
            cmd.bodyTurnRemaining = angle;
            cmd.distanceRemaining = distanceScale(distance, angle) * dir;
            return true;
        }

        public void onPaint(Graphics2D g) {
            if (!paintMovement || movements == null || movements.isEmpty()) {
                return;
            }
            if (paintWaveRisk != paintEnemyRisk) {
                g.drawString(paintEnemyRisk ? "enemy" : "wave", 20, 20);
            }
//			Stroke prevStroke = g.getStroke();
//			g.setStroke(new BasicStroke(0.1f));
            ToDoubleFunction<Movement> risk =
                    (paintEnemyRisk == paintWaveRisk) ? m -> m.risk
                            : paintWaveRisk ? m -> m.waveRisk
                            : paintEnemyRisk ? m -> m.enemyRisk : m -> m.risk;
            double maxRisk = movements.stream().mapToDouble(risk).max().getAsDouble();
            Color[] colors = new Color[]{Color.black, Color.blue, Color.green, Color.yellow, Color.orange, Color.red};
            for (Movement movement : movements) {
                g.setColor(colors[(int) Math.floor(risk.applyAsDouble(movement) / maxRisk * 5.0)]);
                movement.data.stream()
                        .filter(p -> p.location.distance(robots.self.location) >= 20.0)
                        .forEach(p -> g.drawOval((int) Math.round(p.location.x) - 2, (int) Math.round(p.location.y) - 2, 4, 4));
                g.setColor(Color.white);
                movement.waveHitPoints.stream()
                        .map(hd -> hd.data.location)
                        .forEach(p -> g.drawOval((int) Math.round(p.x) - 2, (int) Math.round(p.y) - 2, 4, 4));
            }
//			g.setStroke(prevStroke);
        }

        static class Movement {
            Point target;
            List<Data> data;
            double enemyRisk;
            double waveRisk;
            double risk;
            List<HitData> waveHitPoints;

            public String toString() {
                return "Movement[target=" + target + ", risk=" + risk + "]";
            }
        }
    }

    Robots robots;
    Radar radar;
    MeleeStrategy strategy;
    List<Event> events = new ArrayList<>();

    public void init() {
        MAX_X = MovementInterpolator.battleFieldWidth = getBattleFieldWidth();
        MAX_Y = MovementInterpolator.battleFieldHeight = getBattleFieldHeight();
        BATTLEFIELD = new Rect(WALL_MIN_DIST, WALL_MIN_DIST, MAX_X - WALL_MIN_DIST * 2.0, MAX_Y - WALL_MIN_DIST * 2.0);
        GUN_COOLING_RATE = getGunCoolingRate();

        setAllColors(Color.MAGENTA);

        nbRounds++;
        printf("Round: %d", nbRounds);

        setAdjustGunForRobotTurn(true);
        setAdjustRadarForRobotTurn(true);
        setAdjustRadarForGunTurn(true);
        setScanColor(Color.MAGENTA);

        robots = new Robots(this);
        radar = new MeleeRadar(this, robots);
        strategy = new MeleeStrategy(this, robots);
    }

    public void run() {
        init();
        while (true) {
            if (!events.isEmpty()) {
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
            strategy.run(events);
        }
        radar.run(events);
//		out.println("Body heading: " + getHeading());
//		out.println("Gun heading: " + getGunHeading());
//		out.println("Radar heading: " + getRadarHeading());
//		out.println("Movement: " + movement.toString());
//		out.println("Radar: " + radar.toString());
//		out.println("Gun: " + gun.toString());
    }

    Map<String, Color> colors = new HashMap<>();

    @Override
    public void onPaint(Graphics2D g) {
        radar.onPaint(g);
        strategy.onPaint(g);
        long time = getTime();
        for (Robot r : robots.robots().collect(Collectors.toList())) {
            for (Wave w : r.waves) {
                for (long fireTime = w.timeMin; fireTime <= w.timeMax; fireTime++) {
                    double d = (time - fireTime) * w.bulletSpeed;
                    g.setColor(colors.computeIfAbsent(r.name, this::getEnemyColor));
                    Point location = r.getLocation(fireTime - 1);
                    g.drawOval((int) Math.round(location.x - d), (int) Math.round(location.y - d),
                            (int) Math.round(d * 2), (int) Math.round(d * 2));
                }
                double[] bins = w.calcDangers(robots.self.location);
                double maxD = max(bins);
                if (maxD > 0.0) {
                    double GF0 = absoluteBearing(r.getLocation(w.timeMin), robots.self.getLocation(w.timeMin));
                    double MEA = maxEscapeAngle(w.bulletSpeed);
                    double a1 = GF0 - MEA;
                    double a2 = GF0 + MEA;
                    int index1 = (int) ((180 / Math.PI) * a1 + 360) % 360;
                    int index2 = (int) ((180 / Math.PI) * a2 + 360) % 360;
                    Color[] colors = new Color[]{Color.black, Color.blue, Color.green, Color.yellow, Color.orange, Color.red};
                    for (int i = 0; i < bins.length; i++) {
                        if ((index1 < i && i < index2) || ((index2 < index1) && (index1 < i || i < index2))) {
                            double danger = bins[i] * w.botShadowBins[i] / maxD;
                            Point location = r.getLocation(w.timeMin - 1);
                            double d = (time - w.timeMin) * w.bulletSpeed;
                            Point p = location.add(Vector.fromDM(i * Math.PI / 180, d));
                            g.setColor(colors[(int) Math.floor(danger * 5.0)]);
                            g.drawOval((int) Math.round(p.x) - 3, (int) Math.round(p.y) - 3, 6, 6);
                        }
                    }
                }
            }
        }

    }

    private Color getEnemyColor(String name) {
        return Color.getHSBColor(colors.size() / (float) robots.robots.size(), 0.8f, 0.8f);
    }

    public void onCustomEvent(CustomEvent arg0) {
        events.add(arg0);
    }

    public void onMessageReceived(MessageEvent arg0) {
        events.add(arg0);
    }

    public void onBulletHit(BulletHitEvent arg0) {
        events.add(arg0);
    }

    public void onBulletHitBullet(BulletHitBulletEvent arg0) {
        events.add(arg0);
    }

    public void onBulletMissed(BulletMissedEvent arg0) {
        events.add(arg0);
    }

    public void onDeath(DeathEvent arg0) {
        events.add(arg0);
    }

    public void onHitByBullet(HitByBulletEvent arg0) {
        events.add(arg0);
    }

    public void onHitRobot(HitRobotEvent arg0) {
        events.add(arg0);
    }

    public void onHitWall(HitWallEvent arg0) {
        events.add(arg0);
    }

    public void onRobotDeath(RobotDeathEvent arg0) {
        events.add(arg0);
    }

    public void onScannedRobot(ScannedRobotEvent arg0) {
        events.add(arg0);
    }

    public void onStatus(StatusEvent arg0) {
        events.add(arg0);
    }

    public void onWin(WinEvent arg0) {
        events.add(arg0);
    }

    public void onSkippedTurn(SkippedTurnEvent arg0) {
        events.add(arg0);
        printf("WARNING! Turn skipped!");
    }

    @Override
    public void onKeyPressed(KeyEvent e) {
        events.add(new KeyPressedEvent(e));
    }

    @Override
    public void onKeyReleased(KeyEvent e) {
        events.add(new KeyReleasedEvent(e));
    }

    @Override
    public void onKeyTyped(KeyEvent e) {
        events.add(new KeyTypedEvent(e));
    }

    public void printf(String msg, Object... args) {
        out.printf("%3d %s%n", getTime(), String.format(msg, args));
    }

    private static <T> List<T> lastN(List<T> list, int n) {
        return list.subList(Math.max(0, list.size() - n), list.size());
    }

    public static double limit(double min, double value, double max) {
        return Math.max(min, Math.min(value, max));
    }

    public static boolean eq(double d0, double d1) {
        return Math.abs(d0 - d1) <= NEAR_DELTA;
    }

    public static boolean between(double d0, double d1, double d2) {
        return d0 - NEAR_DELTA <= d1 && d1 <= d2 + NEAR_DELTA;
    }

    // got this from RaikoMicro, by Jamougha, but I think it's used by many authors
    //  - returns the absolute angle (in radians) from source to target points
    public static double absoluteBearing(Point source, Point target) {
        return Math.atan2(target.x - source.x, target.y - source.y);
    }

    public static double distanceScale(double oldDistance, double changeAngle) {
        return Math.min(sqr(sqr(Math.cos(changeAngle))) * 19, oldDistance);
    }

    public static double sqr(double d) {
        return d * d;
    }

    static double maxEscapeAngle(double velocity) {
        return Math.asin(8.0 / velocity);
    }

    static double max(double[] bins) {
        return DoubleStream.of(bins).max().getAsDouble();
    }

    static void normalizeArea(double[] bins) {
        double total = 0.0;
        for (int i = 0; i < bins.length; i++) {
            if (bins[i] != Double.POSITIVE_INFINITY) {
                total += bins[i];
            }
        }
        if (total != 0) {
            double invTotal = 1.0 / total;
            for (int i = 0; i < bins.length; i++)
                if (bins[i] != Double.POSITIVE_INFINITY) {
                    bins[i] *= invTotal;
                }
        }
    }

    static <T> void normalizeMax(Collection<T> collection, ToDoubleFunction<T> getter, BiConsumer<T, Double> setter) {
        OptionalDouble max = collection.stream()
                .mapToDouble(getter)
                .filter(r -> r > 0.0 && r < Double.POSITIVE_INFINITY)
                .max();
        if (max.isPresent()) {
            collection.forEach(m -> setter.accept(m, getter.applyAsDouble(m) / max.getAsDouble()));
        }
    }

    static <T> void normalizeMedian(Collection<T> collection, ToDoubleFunction<T> getter, BiConsumer<T, Double> setter) {
        double[] values = collection.stream()
                .mapToDouble(getter)
                .filter(r -> r > 0.0 && r < Double.POSITIVE_INFINITY)
                .sorted()
                .toArray();
        if (values.length > 0) {
            double median = values.length % 2 == 0
                    ? (values[values.length / 2 - 1] + values[values.length / 2]) / 2.0
                    : values[values.length / 2];
            if (median > 0.0) {
                collection.forEach(m -> setter.accept(m, getter.applyAsDouble(m) / median));
            }
        }
    }

    /**
     * This class implements the <a href="http://mathworld.wolfram.com/BrentsMethod.html">
     * Brent algorithm</a> for finding zeros of real univariate functions.
     * The function should be continuous but not necessarily smooth.
     * The {@code solve} method returns a zero {@code x} of the function {@code f}
     * in the given interval {@code [a, b]} to within a tolerance
     * {@code 2 eps abs(x) + t} where {@code eps} is the relative accuracy and
     * {@code t} is the absolute accuracy.
     * <p>The given interval must bracket the root.</p>
     * <p>
     *  The reference implementation is given in chapter 4 of
     *  <blockquote>
     *   <b>Algorithms for Minimization Without Derivatives</b>,
     *   <em>Richard P. Brent</em>,
     *   Dover, 2002
     *  </blockquote>
     */
    public static class BrentSolver {

        /** Default absolute accuracy. */
        private static final double DEFAULT_ABSOLUTE_ACCURACY = 1e-6;

        /** Default relative accuracy. */
        private static final double DEFAULT_RELATIVE_ACCURACY = 1e-14;
        /** Default function value accuracy. */
        private static final double DEFAULT_FUNCTION_VALUE_ACCURACY = 1e-15;
        /** function value accuracy. */
        private final double functionValueAccuracy;
        /** Absolute accuracy. */
        private final double absoluteAccuracy;
        /** Relative accuracy. */
        private final double relativeAccuracy;
        /** Lower end of search interval. */
        private double searchMin;
        /** Higher end of search interval. */
        private double searchMax;
        /** Initial guess. */
        private double searchStart;
        /** Function to solve. */
        private DoubleUnaryOperator function;

        /**
         * Construct a solver with default absolute accuracy (1e-6).
         */
        public BrentSolver() {
            this(DEFAULT_ABSOLUTE_ACCURACY);
        }
        /**
         * Construct a solver.
         *
         * @param absoluteAccuracy Absolute accuracy.
         */
        public BrentSolver(double absoluteAccuracy) {
            this(DEFAULT_RELATIVE_ACCURACY,
                    absoluteAccuracy,
                    DEFAULT_FUNCTION_VALUE_ACCURACY);
        }
        /**
         * Construct a solver.
         *
         * @param relativeAccuracy Relative accuracy.
         * @param absoluteAccuracy Absolute accuracy.
         */
        public BrentSolver(double relativeAccuracy,
                           double absoluteAccuracy) {
            this(relativeAccuracy, absoluteAccuracy, DEFAULT_FUNCTION_VALUE_ACCURACY);
        }
        /**
         * Construct a solver.
         *
         * @param relativeAccuracy Relative accuracy.
         * @param absoluteAccuracy Absolute accuracy.
         * @param functionValueAccuracy Function value accuracy.
         */
        public BrentSolver(double relativeAccuracy,
                           double absoluteAccuracy,
                           double functionValueAccuracy) {
            this.absoluteAccuracy      = absoluteAccuracy;
            this.relativeAccuracy      = relativeAccuracy;
            this.functionValueAccuracy = functionValueAccuracy;
        }

        public double solve(int maxEval, DoubleUnaryOperator f, double min, double max) {
            return solve(maxEval, f, min, max, min + 0.5 * (max - min));
        }

        /** {@inheritDoc} */
        public double solve(int maxEval, DoubleUnaryOperator f, double startValue) {
            return solve(maxEval, f, Double.NaN, Double.NaN, startValue);
        }

        public double solve(int maxEval, DoubleUnaryOperator f, double min, double max, double startValue) {
            // Initialization.
            setup(maxEval, f, min, max, startValue);
            // Perform computation.
            return doSolve();
        }

        /**
         * Prepare for computation.
         * Subclasses must call this method if they override any of the
         * {@code solve} methods.
         *
         * @param f function to solve.
         * @param min Lower bound for the interval.
         * @param max Upper bound for the interval.
         * @param startValue Start value to use.
         * @param maxEval Maximum number of evaluations.
         */
        protected void setup(int maxEval,
                             DoubleUnaryOperator f,
                             double min, double max,
                             double startValue) {
            // Reset.
            searchMin = min;
            searchMax = max;
            searchStart = startValue;
            function = Objects.requireNonNull(f);
        }

        /**
         * Compute the objective function value.
         *
         * @param point Point at which the objective function must be evaluated.
         * @return the objective function value at specified point.
         * is exceeded.
         */
        protected double computeObjectiveValue(double point) {
            return function.applyAsDouble(point);
        }

        protected double doSolve() {
            double min = this.searchMin;
            double max = this.searchMax;
            final double initial = this.searchStart;
            final double functionValueAccuracy = this.functionValueAccuracy;

            if (min >= initial || initial >= max) {
                throw new IllegalArgumentException("Illegal value range");
            }

            // Return the initial guess if it is good enough.
            double yInitial = computeObjectiveValue(initial);
            if (abs(yInitial) <= functionValueAccuracy) {
                return initial;
            }

            // Return the first endpoint if it is good enough.
            double yMin = computeObjectiveValue(min);
            if (abs(yMin) <= functionValueAccuracy) {
                return min;
            }

            // Reduce interval if min and initial bracket the root.
            if (yInitial * yMin < 0) {
                return brent(min, initial, yMin, yInitial);
            }

            // Return the second endpoint if it is good enough.
            double yMax = computeObjectiveValue(max);
            if (abs(yMax) <= functionValueAccuracy) {
                return max;
            }

            // Reduce interval if initial and max bracket the root.
            if (yInitial * yMax < 0) {
                return brent(initial, max, yInitial, yMax);
            }

            throw new IllegalArgumentException(String.format(
                    "function values at endpoints do not have different signs, endpoints: [{0}, {1}], values: [{2}, {3}]",
                    min, max, yMin, yMax));
        }

        /**
         * Search for a zero inside the provided interval.
         * This implementation is based on the algorithm described at page 58 of
         * the book
         * <blockquote>
         *  <b>Algorithms for Minimization Without Derivatives</b>,
         *  <it>Richard P. Brent</it>,
         *  Dover 0-486-41998-3
         * </blockquote>
         *
         * @param lo Lower bound of the search interval.
         * @param hi Higher bound of the search interval.
         * @param fLo Function value at the lower bound of the search interval.
         * @param fHi Function value at the higher bound of the search interval.
         * @return the value where the function is zero.
         */
        private double brent(double lo, double hi,
                             double fLo, double fHi) {
            double a = lo;
            double fa = fLo;
            double b = hi;
            double fb = fHi;
            double c = a;
            double fc = fa;
            double d = b - a;
            double e = d;

            final double t = this.absoluteAccuracy;
            final double eps = this.relativeAccuracy;

            while (true) {
                if (abs(fc) < abs(fb)) {
                    a = b;
                    b = c;
                    c = a;
                    fa = fb;
                    fb = fc;
                    fc = fa;
                }

                final double tol = 2 * eps * abs(b) + t;
                final double m = 0.5 * (c - b);

                if (abs(m) <= tol ||
                    Precision.equals(fb, 0))  {
                    return b;
                }
                if (abs(e) < tol ||
                    abs(fa) <= abs(fb)) {
                    // Force bisection.
                    d = m;
                    e = d;
                } else {
                    double s = fb / fa;
                    double p;
                    double q;
                    // The equality test (a == c) is intentional,
                    // it is part of the original Brent's method and
                    // it should NOT be replaced by proximity test.
                    if (a == c) {
                        // Linear interpolation.
                        p = 2 * m * s;
                        q = 1 - s;
                    } else {
                        // Inverse quadratic interpolation.
                        q = fa / fc;
                        final double r = fb / fc;
                        p = s * (2 * m * q * (q - r) - (b - a) * (r - 1));
                        q = (q - 1) * (r - 1) * (s - 1);
                    }
                    if (p > 0) {
                        q = -q;
                    } else {
                        p = -p;
                    }
                    s = e;
                    e = d;
                    if (p >= 1.5 * m * q - abs(tol * q) ||
                        p >= abs(0.5 * s * q)) {
                        // Inverse quadratic interpolation gives a value
                        // in the wrong direction, or progress is slow.
                        // Fall back to bisection.
                        d = m;
                        e = d;
                    } else {
                        d = p / q;
                    }
                }
                a = b;
                fa = fb;

                if (abs(d) > tol) {
                    b += d;
                } else if (m > 0) {
                    b += tol;
                } else {
                    b -= tol;
                }
                fb = computeObjectiveValue(b);
                if ((fb > 0 && fc > 0) ||
                    (fb <= 0 && fc <= 0)) {
                    c = a;
                    fc = fa;
                    d = b - a;
                    e = d;
                }
            }
        }
    }

    public static class Data {

        public final long time;
        public final Point location;
        public final Vector velocity;
        public final boolean scan;
        public final Boolean hitBot;
        public final Boolean hitWall;
        public final Boolean hitBullet;
        public final Boolean fired;
        public final Double energy;
        public final Double deltaEnergy;
        public final Double deltaHeading;
        public final Double heat;

        public Data(long time, Point location, Vector velocity) {
            this(time, false, location, velocity, null, null, null, null, null, null, null, null);
        }

        public Data(long time, Point location, Vector velocity, double deltaHeading) {
            this(time, false, location, velocity, null, null, null, null, null, null, null, deltaHeading);
        }

        public Data(long time, Point location, Vector velocity, double energy, double heat, double deltaHeading) {
            this(time, true, location, velocity, energy, heat, null, null, null, null, null, deltaHeading);
        }

        private Data(long time, boolean scan, Point location, Vector velocity, Double energy, Double heat, Boolean hitBot, Boolean hitWall, Boolean hitBullet, Boolean fired, Double deltaEnergy, Double deltaHeading) {
            this.time = time;
            this.location = location;
            this.velocity = velocity;
            this.scan = scan;
            this.energy = energy != null ? roundComputeErrors(energy) : null;
            this.heat = heat != null ? roundComputeErrors(heat) : null;
            this.hitBot = hitBot;
            this.hitWall = hitWall;
            this.hitBullet = hitBullet;
            this.fired = fired;
            this.deltaEnergy = deltaEnergy;
            this.deltaHeading = deltaHeading;
        }

        public Data energy(double energy) {
            return this.energy != null && this.energy == energy
                    ? this : new Data(time, scan, location, velocity, energy, heat, hitBot, hitWall, hitBullet, fired, deltaEnergy, deltaHeading);
        }

        public Data hitBot(boolean hitBot) {
            return this.hitBot != null && this.hitBot == hitBot
                    ? this : new Data(time, scan, location, velocity, energy, heat, hitBot, hitWall, hitBullet, fired, deltaEnergy, deltaHeading);
        }

        public Boolean hitBot() {
            return hitBot;
        }

        public Data hitWall(boolean hitWall) {
            return this.hitWall != null && this.hitWall == hitWall
                    ? this : new Data(time, scan, location, velocity, energy, heat, hitBot, hitWall, hitBullet, fired, deltaEnergy, deltaHeading);
        }

        public Boolean hitWall() {
            return hitWall;
        }

        public Data hitBullet(boolean hitBullet) {
            return this.hitBullet != null && this.hitBullet == hitBullet
                    ? this : new Data(time, scan, location, velocity, energy, heat, hitBot, hitWall, hitBullet, fired, deltaEnergy, deltaHeading);
        }

        public Boolean hitBullet() {
            return hitBullet;
        }

        public Data fired(boolean fired) {
            return this.fired != null && this.fired == fired
                    ? this : new Data(time, scan, location, velocity, energy, heat, hitBot, hitWall, hitBullet, fired, deltaEnergy, deltaHeading);
        }

        public Boolean fired() {
            return fired;
        }

        public Data deltaEnergy(double deltaEnergy) {
            return this.deltaEnergy != null && this.deltaEnergy == deltaEnergy
                    ? this : new Data(time, scan, location, velocity, energy, heat, hitBot, hitWall, hitBullet, fired, deltaEnergy, deltaHeading);
        }

        public Data deltaHeading(double deltaHeading) {
            return this.deltaHeading != null && this.deltaHeading == deltaHeading
                    ? this : new Data(time, scan, location, velocity, energy, heat, hitBot, hitWall, hitBullet, fired, deltaEnergy, deltaHeading);
        }

        @Override
        public String toString() {
            return "Data{" +
                    "time=" + time +
                    ", scan=" + scan +
                    ", location=" + location +
                    ", velocity=" + velocity +
                    (energy != null ? ", energy=" + energy : "") +
                    (heat != null ? ", heat=" + heat : "") +
                    (hitBot != null && hitBot ? ", hitBot" : "") +
                    (hitWall != null && hitWall ? ", hitWall" : "") +
                    (hitBullet != null && hitBullet ? ", hitBullet" : "") +
                    (fired != null && fired ? ", fired" : "") +
                    (deltaEnergy != null ? ", deltaEnergy=" + deltaEnergy : "") +
                    '}';
        }

        public String toCreateString() {
            return String.format("new Data(%d, Point.fromXY(%a, %a), Vector.fromDM(%a, %a))",
                    time, location.x, location.y, velocity.d, velocity.m);
        }
    }

    public abstract static class KDTree<T> {

        // use a big bucketSize so that we have less node bounds (for more cache
        // hits) and better splits
        // if you have lots of dimensions this should be big, and if you have few small
        private static final int _bucketSize = 50;

        private final int _dimensions;
        private int _nodes;
        private final Node root;
        private final ArrayList<Node> nodeList = new ArrayList<>();

        // prevent GC from having to collect _bucketSize*dimensions*sizeof(double) bytes each
        // time a leaf splits
        private double[] mem_recycle;

        // the starting values for bounding boxes, for easy access
        private final double[] bounds_template;

        // one big self-expanding array to keep all the node bounding boxes so that
        // they stay in cache
        // node bounds available at:
        // low: 2 * _dimensions * node.index + 2 * dim
        // high: 2 * _dimensions * node.index + 2 * dim + 1
        private final ContiguousDoubleArrayList nodeMinMaxBounds;

        private KDTree(int dimensions) {
            _dimensions = dimensions;

            nodeMinMaxBounds = new ContiguousDoubleArrayList(1024 / 8 + 2 * _dimensions);
            mem_recycle = new double[_bucketSize * dimensions];

            bounds_template = new double[2 * _dimensions];
            Arrays.fill(bounds_template, Double.NEGATIVE_INFINITY);
            for (int i = 0, max = 2 * _dimensions; i < max; i += 2)
                bounds_template[i] = Double.POSITIVE_INFINITY;

            // and.... start!
            root = new Node();
        }

        public int nodes() {
            return _nodes;
        }

        public int size() {
            return root.entries;
        }

        public int addPoint(double[] location, T payload) {

            Node addNode = root;
            // Do a Depth First Search to find the Node where 'location' should be
            // stored
            while (addNode.pointLocations == null) {
                addNode.expandBounds(location);
                if (location[addNode.splitDim] < addNode.splitVal)
                    addNode = nodeList.get(addNode.lessIndex);
                else
                    addNode = nodeList.get(addNode.moreIndex);
            }
            addNode.expandBounds(location);

            int nodeSize = addNode.add(location, payload);

            if (nodeSize % _bucketSize == 0)
                // try splitting again once every time the node passes a _bucketSize
                // multiple
                // in case it is full of points of the same location and won't split
                addNode.split();

            return root.entries;
        }

        public List<SearchResult<T>> nearestNeighbours(double[] searchLocation, int K) {

            K = Math.min(K, size());

            ArrayList<SearchResult<T>> returnResults = new ArrayList<>(K);

            if (K > 0) {
                IntStack stack = new IntStack();
                PrioQueue<T> results = new PrioQueue<>(K, true);

                stack.push(root.index);

                int added = 0;

                while (stack.size() > 0) {
                    int nodeIndex = stack.pop();
                    if (added < K || results.peekPrio() > pointRectDist(nodeIndex, searchLocation)) {
                        Node node = nodeList.get(nodeIndex);
                        if (node.pointLocations == null)
                            node.search(searchLocation, stack);
                        else
                            added += node.search(searchLocation, results);
                    }
                }

                double[] priorities = results.priorities;
                Object[] elements = results.elements;
                for (int i = 0; i < K; i++) { // forward (closest first)
                    SearchResult<T> s = new SearchResult<T>(priorities[i], (T) elements[i]);
                    returnResults.add(s);
                }
            }
            return returnResults;
        }

        public List<T> ballSearch(double[] searchLocation, double radius) {
            IntStack stack = new IntStack();
            ArrayList<T> results = new ArrayList<>();
            stack.push(root.index);
            while (stack.size() > 0) {
                int nodeIndex = stack.pop();
                if (radius > pointRectDist(nodeIndex, searchLocation)) {
                    Node node = nodeList.get(nodeIndex);
                    if (node.pointLocations == null)
                        stack.push(node.moreIndex).push(node.lessIndex);
                    else
                        node.searchBall(searchLocation, radius, results);
                }
            }
            return results;
        }

        public List<T> rectSearch(double[] mins, double[] maxs) {
            IntStack stack = new IntStack();
            ArrayList<T> results = new ArrayList<>();
            stack.push(root.index);
            while (stack.size() > 0) {
                int nodeIndex = stack.pop();
                if (overlaps(mins, maxs, nodeIndex)) {
                    Node node = nodeList.get(nodeIndex);
                    if (node.pointLocations == null)
                        stack.push(node.moreIndex).push(node.lessIndex);
                    else
                        node.searchRect(mins, maxs, results);
                }
            }
            return results;

        }

        abstract double pointRectDist(int offset, final double[] location);

        abstract double pointDist(double[] arr, double[] location, int index);

        boolean contains(double[] arr, double[] mins, double[] maxs, int index) {
            int offset = (index + 1) * mins.length;
            for (int i = mins.length; i-- > 0;) {
                double d = arr[--offset];
                if (mins[i] > d | d > maxs[i])
                    return false;
            }
            return true;
        }

        boolean overlaps(double[] mins, double[] maxs, int offset) {
            offset *= (2 * maxs.length);
            final double[] array = nodeMinMaxBounds.array;
            for (int i = 0; i < maxs.length; i++, offset += 2) {
                double bmin = array[offset], bmax = array[offset + 1];
                if (mins[i] > bmax | maxs[i] < bmin)
                    return false;
            }
            return true;
        }

        public static class Euclidean<T> extends KDTree<T> {
            public Euclidean(int dims) {
                super(dims);
            }

            double pointRectDist(int offset, final double[] location) {
                offset *= (2 * super._dimensions);
                double distance = 0;
                final double[] array = super.nodeMinMaxBounds.array;
                for (int i = 0; i < location.length; i++, offset += 2) {

                    double diff = 0;
                    double bv = array[offset];
                    double lv = location[i];
                    if (bv > lv)
                        diff = bv - lv;
                    else {
                        bv = array[offset + 1];
                        if (lv > bv)
                            diff = lv - bv;
                    }
                    distance += sqr(diff);
                }
                return distance;
            }

            double pointDist(double[] arr, double[] location, int index) {
                double distance = 0;
                int offset = (index + 1) * super._dimensions;

                for (int i = super._dimensions; i-- > 0;) {
                    distance += sqr(arr[--offset] - location[i]);
                }
                return distance;
            }

        }

        public static class Manhattan<T> extends KDTree<T> {
            public Manhattan(int dims) {
                super(dims);
            }

            double pointRectDist(int offset, final double[] location) {
                offset *= (2 * super._dimensions);
                double distance = 0;
                final double[] array = super.nodeMinMaxBounds.array;
                for (int i = 0; i < location.length; i++, offset += 2) {

                    double diff = 0;
                    double bv = array[offset];
                    double lv = location[i];
                    if (bv > lv)
                        diff = bv - lv;
                    else {
                        bv = array[offset + 1];
                        if (lv > bv)
                            diff = lv - bv;
                    }
                    distance += (diff);
                }
                return distance;
            }

            double pointDist(double[] arr, double[] location, int index) {
                double distance = 0;
                int offset = (index + 1) * super._dimensions;

                for (int i = super._dimensions; i-- > 0;) {
                    distance += abs(arr[--offset] - location[i]);
                }
                return distance;
            }
        }

        public static class WeightedManhattan<T> extends KDTree<T> {
            private double[] weights;

            public WeightedManhattan(int dims) {
                super(dims);
                weights = new double[dims];
                for (int i = 0; i < dims; i++)
                    weights[i] = 1.0;
            }

            public void setWeights(double[] newWeights) {
                weights = newWeights;
            }

            double pointRectDist(int offset, final double[] location) {
                offset *= (2 * super._dimensions);
                double distance = 0;
                final double[] array = super.nodeMinMaxBounds.array;
                for (int i = 0; i < location.length; i++, offset += 2) {

                    double diff = 0;
                    double bv = array[offset];
                    double lv = location[i];
                    if (bv > lv)
                        diff = bv - lv;
                    else {
                        bv = array[offset + 1];
                        if (lv > bv)
                            diff = lv - bv;
                    }
                    distance += (diff) * weights[i];
                }
                return distance;
            }

            double pointDist(double[] arr, double[] location, int index) {
                double distance = 0;
                int offset = (index + 1) * super._dimensions;

                for (int i = super._dimensions; i-- > 0;) {
                    distance += abs(arr[--offset] - location[i]) * weights[i];
                }
                return distance;
            }
        }

        public static class SearchResult<S> {
            public final double distance;
            public final S payload;

            SearchResult(double dist, S load) {
                distance = dist;
                payload = load;
            }

            public double getDistance() {
                return distance;
            }

            public S getPayload() {
                return payload;
            }
        }

        private class Node {

            // for accessing bounding box data
            // - if trees weren't so unbalanced might be better to use an implicit
            // heap?
            int index;

            // keep track of size of subtree
            int entries;

            // leaf
            ContiguousDoubleArrayList pointLocations;
            ArrayList<T> pointPayloads = new ArrayList<>(_bucketSize);

            // stem
            // Node less, more;
            int lessIndex, moreIndex;
            int splitDim;
            double splitVal;

            Node() {
                this(new double[_bucketSize * _dimensions]);
            }

            Node(double[] pointMemory) {
                pointLocations = new ContiguousDoubleArrayList(pointMemory);
                index = _nodes++;
                nodeList.add(this);
                nodeMinMaxBounds.add(bounds_template);
            }

            void search(double[] searchLocation, IntStack stack) {
                if (searchLocation[splitDim] < splitVal)
                    stack.push(moreIndex).push(lessIndex); // less will be popped
                // first
                else
                    stack.push(lessIndex).push(moreIndex); // more will be popped
                // first
            }

            // returns number of points added to results
            int search(double[] searchLocation, PrioQueue<T> results) {
                int updated = 0;
                for (int j = entries; j-- > 0;) {
                    double distance = pointDist(pointLocations.array, searchLocation, j);
                    if (results.peekPrio() > distance) {
                        updated++;
                        results.addNoGrow(pointPayloads.get(j), distance);
                    }
                }
                return updated;
            }

            void searchBall(double[] searchLocation, double radius, ArrayList<T> results) {
                for (int j = entries; j-- > 0;) {
                    double distance = pointDist(pointLocations.array, searchLocation, j);
                    if (radius >= distance) {
                        results.add(pointPayloads.get(j));
                    }
                }
            }

            void searchRect(double[] mins, double[] maxs, ArrayList<T> results) {
                for (int j = entries; j-- > 0;)
                    if (contains(pointLocations.array, mins, maxs, j))
                        results.add(pointPayloads.get(j));
            }

            void expandBounds(double[] location) {
                entries++;
                int mio = index * 2 * _dimensions;
                for (int i = 0; i < _dimensions; i++) {
                    nodeMinMaxBounds.array[mio] = Math.min(nodeMinMaxBounds.array[mio], location[i]);
                    mio++;
                    nodeMinMaxBounds.array[mio] = Math.max(nodeMinMaxBounds.array[mio], location[i]);
                    mio++;
                }
            }

            int add(double[] location, T load) {
                pointLocations.add(location);
                pointPayloads.add(load);
                return entries;
            }

            void split() {
                int offset = index * 2 * _dimensions;

                double diff = 0;
                for (int i = 0; i < _dimensions; i++) {
                    double min = nodeMinMaxBounds.array[offset];
                    double max = nodeMinMaxBounds.array[offset + 1];
                    if (max - min > diff) {
                        double mean = 0;
                        for (int j = 0; j < entries; j++)
                            mean += pointLocations.array[i + _dimensions * j];

                        mean = mean / entries;
                        double varianceSum = 0;

                        for (int j = 0; j < entries; j++)
                            varianceSum += sqr(mean - pointLocations.array[i + _dimensions * j]);

                        if (varianceSum > diff * entries) {
                            diff = varianceSum / entries;
                            splitVal = mean;

                            splitDim = i;
                        }
                    }
                    offset += 2;
                }

                // kill all the nasties
                if (splitVal == Double.POSITIVE_INFINITY)
                    splitVal = Double.MAX_VALUE;
                else if (splitVal == Double.NEGATIVE_INFINITY)
                    splitVal = Double.MIN_VALUE;
                else if (splitVal == nodeMinMaxBounds.array[index * 2 * _dimensions + 2 * splitDim + 1])
                    splitVal = nodeMinMaxBounds.array[index * 2 * _dimensions + 2 * splitDim];

                Node less = new Node(mem_recycle); // recycle that memory!
                Node more = new Node();
                lessIndex = less.index;
                moreIndex = more.index;

                // reduce garbage by factor of _bucketSize by recycling this array
                double[] pointLocation = new double[_dimensions];
                for (int i = 0; i < entries; i++) {
                    System.arraycopy(pointLocations.array, i * _dimensions, pointLocation, 0, _dimensions);
                    T load = pointPayloads.get(i);

                    if (pointLocation[splitDim] < splitVal) {
                        less.expandBounds(pointLocation);
                        less.add(pointLocation, load);
                    }
                    else {
                        more.expandBounds(pointLocation);
                        more.add(pointLocation, load);
                    }
                }
                if (less.entries * more.entries == 0) {
                    // one of them was 0, so the split was worthless. throw it away.
                    _nodes -= 2; // recall that bounds memory
                    nodeList.remove(moreIndex);
                    nodeList.remove(lessIndex);
                }
                else {

                    // we won't be needing that now, so keep it for the next split
                    // to reduce garbage
                    mem_recycle = pointLocations.array;

                    pointLocations = null;

                    pointPayloads.clear();
                    pointPayloads = null;
                }
            }

        }

        // NB! This Priority Queue keeps things with the LOWEST priority.
        // If you want highest priority items kept, negate your values
        private static class PrioQueue<S> {

            Object[] elements;
            double[] priorities;
            private double minPrio;
            private int size;

            PrioQueue(int size, boolean prefill) {
                elements = new Object[size];
                priorities = new double[size];
                Arrays.fill(priorities, Double.POSITIVE_INFINITY);
                if (prefill) {
                    minPrio = Double.POSITIVE_INFINITY;
                    this.size = size;
                }
            }

            // uses O(log(n)) comparisons and one big shift of size O(N)
            // and is MUCH simpler than a heap --> faster on small sets, faster JIT

            void addNoGrow(S value, double priority) {
                int index = searchFor(priority);
                int nextIndex = index + 1;
                int length = size - nextIndex;
                System.arraycopy(elements, index, elements, nextIndex, length);
                System.arraycopy(priorities, index, priorities, nextIndex, length);
                elements[index] = value;
                priorities[index] = priority;

                minPrio = priorities[size - 1];
            }

            int searchFor(double priority) {
                int i = size - 1;
                int j = 0;
                while (i >= j) {
                    int index = (i + j) >>> 1;
                    if (priorities[index] < priority)
                        j = index + 1;
                    else
                        i = index - 1;
                }
                return j;
            }

            double peekPrio() {
                return minPrio;
            }
        }

        private static class ContiguousDoubleArrayList {
            double[] array;
            int size;

            ContiguousDoubleArrayList(int size) {
                this(new double[size]);
            }

            ContiguousDoubleArrayList(double[] data) {
                array = data;
            }

            ContiguousDoubleArrayList add(double[] da) {
                if (size + da.length > array.length)
                    array = Arrays.copyOf(array, (array.length + da.length) * 2);

                System.arraycopy(da, 0, array, size, da.length);
                size += da.length;
                return this;
            }
        }

        private static class IntStack {
            int[] array;
            int size;

            IntStack() {
                this(64);
            }

            IntStack(int size) {
                this(new int[size]);
            }

            IntStack(int[] data) {
                array = data;
            }

            IntStack push(int i) {
                if (size >= array.length)
                    array = Arrays.copyOf(array, (array.length + 1) * 2);

                array[size++] = i;
                return this;
            }

            int pop() {
                return array[--size];
            }

            int size() {
                return size;
            }
        }

        static double sqr(double d) {
            return d * d;
        }

    }

    public static class MovementInterpolator {

        public static double ROBOT_SIZE = 36.0;
        public static final double NEAR_DELTA = .00001;
        public static final double DELTA = 1E-4;
        public static final double SIM_DELTA = 0.1;

        public static double battleFieldWidth;
        public static double battleFieldHeight;

        public static class Command {
            public double bodyTurnRemaining;
            public double distanceRemaining;
            public double maxTurnRate = Rules.MAX_TURN_RATE;
            public double maxVelocity = Rules.MAX_VELOCITY;
        }

        public static List<Data> interpolate(Data start, Data end) {
            List<Data> sim = doInterpolate(start, end);
            if (sim != null) {
                // Check collisions
                double energy = start.energy;
                for (int i = 1; i < sim.size(); i++) {
                    Data s = sim.get(i - 1);
                    Data e = sim.get(i);
                    double m0 = s.velocity.m;
                    double m1 = e.velocity.m;
                    if (e.energy != null) {
                        energy = e.energy;
                    }
                    if (e.hitBot == null && e.hitWall == null) {
                        // Check the the velocity changes are following the rules
                        boolean noVel = isNear(m1, 0.0);
                        boolean valid = isValidVelocityChange(m0, m1);
                        if (!valid) {
                            if (noVel) {
                                if (isOnWall(e.location)) {
                                    e = e.hitBullet(true);
                                    if (!e.scan) {
                                        e.deltaEnergy(- Rules.getWallHitDamage(s.velocity.m));
                                    }
                                } else {
                                    e = e.hitBot(true);
                                    if (!e.scan) {
                                        e.deltaEnergy(- Rules.ROBOT_HIT_DAMAGE);
                                    }
                                }
                            } else {
                                isValidVelocityChange(m0, m1);
                                doInterpolate(start, end);
                                return null;
                            }
                        } else if (!noVel) {
                            e = e.hitBot(false);
                        }
                        sim.set(i, e);
                    }
                }
                for (int i = 1; i < sim.size(); i++) {
                    Data p = sim.get(i - 1);
                    Data c = sim.get(i);
                    sim.set(i, c.deltaHeading(c.velocity.d - p.velocity.d));
                }
                return sim;
            } else {
                doInterpolate(start, end);
            }
            return null;
        }

        public static List<Data> doInterpolate(Data start, Data end) {
            long deltaTime = end.time - start.time;
            // No interpolation needed
            if (deltaTime <= 1) {
                return interpolate0Point(start, end);
            }
            // Just a single missing tick, we have all the data we need
            if (deltaTime == 2) {
                return interpolate1Point(start, end);
            }
            // 2 missing points
            if (deltaTime == 3) {
                List<Data> sim = interpolate2Points(start, end);
                if (sim != null) {
                    return sim;
                }
            }
            // Try a constant speed
            if (start.velocity.m == end.velocity.m) {
                double maxTurnRate = Rules.MAX_TURN_RATE_RADIANS;
                double turnRate = min(maxTurnRate, (.4 + .6 * (1 - (abs(start.velocity.m) / Rules.MAX_VELOCITY))) * Rules.MAX_TURN_RATE_RADIANS);
                if (deltaTime == 3 && abs(start.velocity.m) == Rules.MAX_VELOCITY) {
                    Function<Vector,Vector> norm = v -> (start.velocity.m < 0) ? Vector.fromDM(v.d + PI, - v.m) : v;
                    Point l0 = start.location;
                    Point l2 = end.location.add(end.velocity, -1);
                    Vector d = l0.sub(l2);
                    Point lm = l0.add(d, 0.5);
                    double dc = d.m / 2.0;
                    if (isNear(dc, start.velocity.m)) {
                        List<Data> sim = Arrays.asList(
                                start,
                                new Data(start.time + 1, lm, norm.apply(l0.sub(lm))),
                                new Data(start.time + 2, l2, norm.apply(lm.sub(l2))),
                                end);
                        return sim;
                    }
                    double dh = sqrt(sq(start.velocity.m) - sq(dc));
                    Point l1a = lm.add(Vector.fromDM(d.d + PI / 2.0, dh));
                    Point l1b = lm.add(Vector.fromDM(d.d - PI / 2.0, dh));
                    Vector dl1a = norm.apply(l0.sub(l1a));
                    Vector dl1b = norm.apply(l0.sub(l1b));
                    List<Data> sima = Arrays.asList(
                            start,
                            new Data(start.time + 1, l1a, dl1a),
                            new Data(start.time + 2, l2, norm.apply(l1a.sub(l2))),
                            end);
                    List<Data> simb = Arrays.asList(
                            start,
                            new Data(start.time + 1, l1b, dl1b),
                            new Data(start.time + 2, l2, norm.apply(l1b.sub(l2))),
                            end);
                    double dd1a = abs(dl1a.d - start.velocity.d);
                    double dd1b = abs(dl1b.d - start.velocity.d);
                    boolean simaValid = dd1a < turnRate;
                    boolean simbValid = dd1b < turnRate;
                    List<Data> sim = null;
                    if (simaValid && simbValid) {
                        if (dd1a < dd1b) {
                            sim = sima;
                        } else {
                            sim = simb;
                        }
                    } else if (simaValid) {
                        sim = sima;
                    } else if (simbValid) {
                        sim = simb;
                    }
                    if (sim != null) {
                        return sim;
                    }
                }
                long nbTurns = (long) ceil(abs(Utils.normalRelativeAngle(end.velocity.d - start.velocity.d)) / turnRate);
                for (long turnTick = start.time; turnTick <= end.time + 1 - nbTurns; turnTick++) {
                    long tt = turnTick;
                    List<Data> sim = simulate(start, deltaTime,
                            (cur, command) -> {
                                if (cur.time == start.time) {
                                    command.distanceRemaining = start.velocity.m > 0 ? Double.POSITIVE_INFINITY : Double.NEGATIVE_INFINITY;
                                    command.maxVelocity = abs(start.velocity.m);
                                }
                                if (cur.time == tt) {
                                    command.bodyTurnRemaining = Utils.normalRelativeAngle(end.velocity.d - start.velocity.d);
                                }
                            });
                    Data last = sim.get(sim.size() - 1);
                    double d = distance(last, end);
                    if (d < SIM_DELTA) {
                        return replaceLast(sim, end);
                    }
                }
                // If none of the above matches, it means there are multiple direction changes,
                // or a maxTurnRate < MAX_TURN_RATE_RADIANS, or a decel/accel
            }
            // Try a simple acceleration / deceleration
            if (end.velocity.m * start.velocity.m >= 0.0) {
                double dv = abs(end.velocity.m) - abs(start.velocity.m);
                // Acceleration
                if (dv == deltaTime * Rules.ACCELERATION || dv < deltaTime * Rules.ACCELERATION && abs(end.velocity.m) == Rules.MAX_VELOCITY) {
                    List<Data> sim = MovementInterpolator.simulate(start, deltaTime, (d, c) -> {
                        if (d.time == start.time) {
                            c.maxVelocity = Rules.MAX_VELOCITY;
                            c.bodyTurnRemaining = Utils.normalRelativeAngle(end.velocity.d - start.velocity.d);
                            c.distanceRemaining = end.velocity.m > 0 ? Double.POSITIVE_INFINITY : Double.NEGATIVE_INFINITY;
                        }
                    });
                    Data last = sim.get(sim.size() - 1);
                    double d = distance(last, end);
                    if (d < SIM_DELTA) {
                        return replaceLast(sim, end);
                    }
                }
                // Deceleration
                if (dv == - deltaTime * Rules.DECELERATION || end.velocity.m == 0.0 || abs(start.velocity.m) == Rules.MAX_VELOCITY) {
                    List<Data> sim = MovementInterpolator.simulate(start, deltaTime, (d, c) -> {
                        if (d.time == start.time) {
                            c.maxVelocity = Rules.MAX_VELOCITY;
                            c.distanceRemaining = 0.0;
                            c.bodyTurnRemaining = Utils.normalRelativeAngle(end.velocity.d - start.velocity.d);
                        }
                    });
                    Data last = sim.get(sim.size() - 1);
                    double d = distance(last, end);
                    if (d < SIM_DELTA) {
                        return replaceLast(sim, end);
                    }
                }
            }
            // Try with a stop / wait? / accel
            if (abs(end.velocity.m) - floor(abs(end.velocity.m)) == 0.0) {
                long dt1 = (long) ceil(abs(start.velocity.m) / Rules.DECELERATION);
                long dt2 = (long) ceil(abs(end.velocity.m) / Rules.ACCELERATION);
                if (deltaTime >= dt1 + dt2) {
                    List<Data> s1 = MovementInterpolator.simulate(start, dt1, (d, c) -> {
                        if (d.time == start.time) {
                            c.maxVelocity = 0;
                            c.bodyTurnRemaining = Utils.normalRelativeAngle(end.velocity.d - start.velocity.d);
                        }
                    });
                    for (long t = start.time + dt1 + 1; t < end.time - dt2; t++) {
                        Data last1 = s1.get(s1.size() - 1);
                        Data d = new Data(t, last1.location, last1.velocity);
                        s1.add(d);
                    }
                    Data last1 = s1.get(s1.size() - 1);
                    List<Data> s2 = MovementInterpolator.simulate(last1, dt2, (d, c) -> {
                        if (d.time == last1.time) {
                            c.maxVelocity = Rules.MAX_VELOCITY;
                            c.bodyTurnRemaining = Utils.normalRelativeAngle(end.velocity.d - last1.velocity.d);
                            c.distanceRemaining = end.velocity.m > 0 ? Double.POSITIVE_INFINITY : Double.NEGATIVE_INFINITY;
                        }
                    });
                    List<Data> sim = Stream.concat(s1.stream(), s2.stream().skip(1)).collect(Collectors.toList());
                    Data last = sim.get(sim.size() - 1);
                    double d = distance(last, end);
                    if (d < SIM_DELTA) {
                        return replaceLast(sim, end);
                    }
                }
            }
    //
    //        VelocityChange vc = getVelocityChange(start, end);
    //        if (vc != null) {
    //            List<Data> sim = simulate(start, deltaTime,
    //                    (cur, command) -> {
    //                        if (cur.time == start.time) {
    //                            command.distanceRemaining = vc.orgDistanceRemaining;
    //                            command.bodyTurnRemaining = vc.commandTick < 0 ? end.velocity.d - start.velocity.d : 0;
    //                        }
    //                        if (cur.time == vc.commandTick) {
    //                            command.bodyTurnRemaining = Utils.normalRelativeAngle(end.velocity.d - start.velocity.d);
    //                            command.distanceRemaining = vc.newDistanceRemaining;
    //                        }
    //                    });
    //            Data last = sim.get(sim.size() - 1);
    //            double d = distance(last, end);
    //            if (d < SIM_DELTA) {
    //                return sim.subList(1, sim.size() - 1);
    //            }
    //        }
    //        if (true) {
    //            return null;
    //        }
    //
    //        List<List<Data>> sims = new ArrayList<>();
    //        for (long t = 0; t <= deltaTime; t++) {
    //            final long ct = start.time + t;
    //            List<Data> sim = simulate(start, deltaTime,
    //                    (cur, command) -> {
    //                        if (cur.time == start.time) {
    //                            command.distanceRemaining = isNear(start.velocity.m, 0.0) ? 0.0 : 100.0 * signum(start.velocity.m);
    //                        }
    //                        if (cur.time == ct) {
    //                            command.bodyTurnRemaining = Utils.normalRelativeAngle(end.velocity.d - start.velocity.d);
    //                            if (isNear(end.velocity.m, 0.0)) {
    //                                command.distanceRemaining = 0;
    //                            } else {
    //                                if (start.velocity.m * end.velocity.m >= 0 && abs(end.velocity.m) < abs(start.velocity.m)) {
    //                                    double dv = abs(end.velocity.m - cur.velocity.m);
    //                                    long dt = end.time - ct;
    //                                    command.distanceRemaining = 0;
    //                                } else {
    //                                    command.distanceRemaining = 100.0 * signum(end.velocity.m);
    //                                }
    //                            }
    //                        }
    //                    });
    //            sims.add(sim);
    //        }
    //        List<Data> sim = sims.stream()
    //                .min(Comparator.comparingDouble(s -> distance(s.get(s.size() - 1), end)))
    //                .orElse(null);
    //        Data last = sim != null ? sim.get(sim.size() - 1) : null;
    //        double d = last != null ? distance(sim.get(sim.size() - 1), end) : Double.POSITIVE_INFINITY;
    //        if (d < SIM_DELTA) {
    //            return sim.subList(1, sim.size() - 1);
    //        }
            return null;
        }

        private static List<Data> replaceLast(List<Data> list, Data end) {
            list.set(list.size() - 1, end);
            return list;
        }

        private static List<Data> interpolate2Points(Data start, Data end) {
            double m0 = start.velocity.m;
            double m1 = Double.NaN;
            double m2 = Double.NaN;
            double m3 = end.velocity.m;
            double am0 = abs(m0);
            double am3 = abs(m3);
            double sm0 = signum(m0);
            double sm3 = signum(m3);
            long deltaTime = end.time - start.time;
            assert deltaTime == 3;
            double dv = (m3 == 0.0 ? - am0 : (m3 - m0) * sm3) / deltaTime;
            if (m0 * m3 >= 0) {
                if (between(-Rules.DECELERATION, dv, Rules.ACCELERATION)) {
                    if (am3 == min(am0 + deltaTime * Rules.ACCELERATION, Rules.MAX_VELOCITY)) {
                        double am1 = min(am0 + Rules.ACCELERATION, Rules.MAX_VELOCITY);
                        m1 = am1 * sm3;
                        m2 = min(am1 + Rules.ACCELERATION, Rules.MAX_VELOCITY) * sm3;
                    } else if (am3 == Math.max(am0 - deltaTime * Rules.DECELERATION, 0.0)) {
                        double am1 = Math.max(am0 - Rules.DECELERATION, 0.0);
                        m1 = am1 * sm0;
                        m2 = Math.max(am1 - Rules.DECELERATION, 0.0) * sm0;
                    } else if (am0 == Rules.MAX_VELOCITY && am3 == Rules.MAX_VELOCITY - Rules.DECELERATION) {
                        m1 = m0;
                        m2 = m0;
                    } else if (am0 == Rules.MAX_VELOCITY && am3 == Rules.MAX_VELOCITY - 2 * Rules.DECELERATION) {
                        m1 = m0;
                        m2 = Math.max(am0 - Rules.DECELERATION, 0.0) * sm0;
                    } else if (am0 == 0.0 && am3 == Rules.ACCELERATION) {
                        m1 = 0;
                        m2 = 0;
                    } else if (am0 == 0.0 && am3 == 2 * Rules.ACCELERATION) {
                        m1 = 0;
                        m2 = Rules.ACCELERATION;
                    } else {
                        DoubleUnaryOperator func = d -> getVelocityAfter(deltaTime, am0, d) - am3;
                        double dist = solve(func, 0.0, 6 * Rules.MAX_VELOCITY);
                        if (!Double.isNaN(dist)) {
                            m1 = getNewVelocity(m0, dist * sm0, Rules.MAX_VELOCITY);
                            m2 = getNewVelocity(m1, dist * sm0 - m1, Rules.MAX_VELOCITY);
                        }
                    }
                }
            } else {
                long dt1 = (long) ceil(am0 / Rules.DECELERATION);
                long dt2 = (long) ceil(am3 / Rules.ACCELERATION);
                if (dt1 == 1 && dt2 == 1) {
                    m1 = 0.0;
                    m2 = 0.0;
                } else if (dt1 == 1 && dt2 == 2) {
                    m1 = 0.0;
                    m2 = Rules.ACCELERATION * sm3;
                } else if (dt1 == 2 && dt2 == 1) {
                    m1 = (am0 - Rules.DECELERATION) * sm0;
                    m2 = 0.0;
                } else {
                    double tm1 = getNewVelocity(m0, sm3 * 100, 8);
                    double tm2 = getNewVelocity(tm1, sm3 * 100, 8);
                    double tm3 = getNewVelocity(tm2, sm3 * 100, 8);
                    if (isNear(tm3, m3)) {
                        m1 = tm1;
                        m2 = tm2;
                    }
                }
            }
            if (!Double.isNaN(m1) && !Double.isNaN(m2)) {
                double maxTurnRate = Rules.MAX_TURN_RATE_RADIANS;
                double tr0 = min(maxTurnRate, (.4 + .6 * (1 - (abs(m0) / Rules.MAX_VELOCITY))) * Rules.MAX_TURN_RATE_RADIANS);
                double tr1 = min(maxTurnRate, (.4 + .6 * (1 - (abs(m1) / Rules.MAX_VELOCITY))) * Rules.MAX_TURN_RATE_RADIANS);
                Point l0 = start.location;
                Point l2 = end.location.add(end.velocity, -1);
                Vector d = l0.sub(l2);
                double d1 = d.m > 0.0 ? d.m / 2.0 + (sq(m1)-sq(m2)) / (2.0 * d.m) : 0.0;
                double d2 = d.m > 0.0 ? d.m / 2.0 - (sq(m1)-sq(m2)) / (2.0 * d.m) : 0.0;
                Point lm = d.m > 0.0 ? l0.add(d, d1 / d.m) : l0;
                List<Data> sim = null;
                if (isNear(abs(m1), d1) && isNear(abs(m2), d2)) {
                    // TODO: if m1 == 0.0 or m2 == 0.0, then l0 == lm or lm == l2
                    // TODO: and the velocity angle can not be computed directly
                    // TODO: and we need to make sure the angle follow the rules
                    sim = Arrays.asList(
                            start,
                            new Data(start.time + 1, lm, l0.sub(lm).relative(start.velocity.d)),
                            new Data(start.time + 2, l2, lm.sub(l2).relative(end.velocity.d)),
                            end);
                } else {
                    double dh = d1 > d2 ? sqrt(sq(m1) - sq(d1)) : sqrt(sq(m2) - sq(d2));
                    Point l1a = lm.add(Vector.fromDM(d.d + PI / 2.0, dh));
                    Point l1b = lm.add(Vector.fromDM(d.d - PI / 2.0, dh));
                    Vector dl1a = l0.sub(l1a).relative(start.velocity.d);
                    Vector dl1b = l0.sub(l1b).relative(start.velocity.d);
                    List<Data> sima = Arrays.asList(
                            start,
                            new Data(start.time + 1, l1a, dl1a),
                            new Data(start.time + 2, l2, l1a.sub(l2).relative(end.velocity.d)),
                            end);
                    List<Data> simb = Arrays.asList(
                            start,
                            new Data(start.time + 1, l1b, dl1b),
                            new Data(start.time + 2, l2, l1b.sub(l2).relative(end.velocity.d)),
                            end);
                    double dd1a = abs(Utils.normalRelativeAngle(dl1a.d - start.velocity.d));
                    double dd2a = abs(Utils.normalRelativeAngle(l1a.sub(l2).relative(end.velocity.d).d - dl1a.d));
                    double dd1b = abs(Utils.normalRelativeAngle(dl1b.d - start.velocity.d));
                    double dd2b = abs(Utils.normalRelativeAngle(l1b.sub(l2).relative(end.velocity.d).d - dl1b.d));
                    boolean simaValid = dd1a <= tr0 + DELTA && dd2a <= tr1 + DELTA;
                    boolean simbValid = dd1b <= tr0 + DELTA && dd2b <= tr1 + DELTA;
                    if (simaValid && simbValid) {
                        if (dd1a + dd2a < dd1b + dd2b) {
                            sim = sima;
                        } else {
                            sim = simb;
                        }
                    } else if (simaValid) {
                        sim = sima;
                    } else if (simbValid) {
                        sim = simb;
                    } else {
                        // TODO: interesting case
                        // the solution is invalid
                        return null;
                    }
                }
                return sim;
            }
            // TODO this is certainly a collision
            if (am3 == 2.0 || am3 == 1.0 || am3 == 0.0) {
                long dt2 = (long) ceil(am3 / Rules.ACCELERATION);
                Point[] locs = new Point[] { start.location, null, end.location.add(end.velocity, -1.0), end.location };
                Vector[] vels = new Vector[] { start.velocity, null, null, end.velocity };
                if (dt2 == 2 && isOnWall(locs[0].add(vels[0]))
                        || dt2 == 1 && isOnWall(locs[2])
                        ||  dt2 == 0 && isOnWall(locs[3])) {
                    List<Data> sim1 = simulate(start, deltaTime, (d, c) -> {
                        if (d.time == start.time) {
                            c.distanceRemaining = m0 < 0.0 ? Double.NEGATIVE_INFINITY : Double.POSITIVE_INFINITY;
                        } else if (d.time == start.time + 3 - dt2) {
                            c.distanceRemaining = m3 < 0.0 ? Double.NEGATIVE_INFINITY : Double.POSITIVE_INFINITY;
                            c.bodyTurnRemaining = normalRelativeAngle(end.velocity.d - d.velocity.d);
                        }
                    });
                    List<Data> sim2 = simulate(start, deltaTime, (d, c) -> {
                        if (d.time == start.time) {
                            c.distanceRemaining = m0 < 0.0 ? Double.NEGATIVE_INFINITY : Double.POSITIVE_INFINITY;
                            c.bodyTurnRemaining = normalRelativeAngle(end.velocity.d - d.velocity.d);
                        } else if (d.time == start.time + 3 - dt2) {
                            c.distanceRemaining = m3 < 0.0 ? Double.NEGATIVE_INFINITY : Double.POSITIVE_INFINITY;
                        }
                    });
                    Data last1 = sim1.get(sim1.size() - 1);
                    double d1 = distance(last1, end);
                    Data last2 = sim2.get(sim2.size() - 1);
                    double d2 = distance(last2, end);
                    List<Data> sim = d1 < d2 ? sim1 : sim2;
                    Data last = d1 < d2 ? last1 : last2;
                    double d = d1 < d2 ? d1 : d2;
                    if (d < SIM_DELTA) {
                        return replaceLast(sim, last.hitWall != null ? end.hitWall(last.hitWall) : end);
                    } else {
                        return null;
                    }
                } else {
                    List<Data> sim1 = simulate(start, 3 - dt2, (d, c) -> {
                        if (d.time == start.time) {
                            c.distanceRemaining = m0 < 0.0 ? Double.NEGATIVE_INFINITY : Double.POSITIVE_INFINITY;
                        }
                    });
                    List<Data> sim2 = simulate(start, 3 - dt2, (d, c) -> {
                        if (d.time == start.time) {
                            c.distanceRemaining = m0 < 0.0 ? Double.NEGATIVE_INFINITY : Double.POSITIVE_INFINITY;
                            c.bodyTurnRemaining = normalRelativeAngle(end.velocity.d - d.velocity.d);
                        }
                    });
                    if (dt2 == 2) {
                        locs[1] = locs[0];
                        vels[1] = Vector.fromDM(vels[0].d, 0.0);
                        vels[2] = locs[1].sub(locs[2]).relative(vels[3].d);
                        return Arrays.asList(
                                start,
                                new Data(start.time + 1, locs[1], vels[1]).hitBot(true),
                                new Data(start.time + 2, locs[2], vels[2]),
                                end
                        );
                    } else if (dt2 == 1) {
                        locs[1] = locs[2];
                        vels[1] = locs[0].sub(locs[1]).relative(vels[0].d);
                        vels[2] = Vector.fromDM(vels[1].d, 0.0);
                        return Arrays.asList(
                                start,
                                new Data(start.time + 1, locs[1], vels[1]),
                                new Data(start.time + 2, locs[2], vels[2]).hitBot(true),
                                end
                        );
                    } else if (dt2 == 0) {
                        return null;
                    }
                }
            }
            return null;
        }

        private static boolean isOnWall(Point loc) {
            return loc.x < ROBOT_SIZE / 2.0 + NEAR_DELTA
                    || loc.y < ROBOT_SIZE / 2.0 + NEAR_DELTA
                    || loc.x > battleFieldWidth - ROBOT_SIZE / 2.0 - NEAR_DELTA
                    || loc.y > battleFieldHeight - ROBOT_SIZE / 2.0 - NEAR_DELTA;
        }

        private static boolean between(double a, double b, double c) {
            return b > a - NEAR_DELTA && b < c + NEAR_DELTA;
        }

        private static List<Data> interpolate1Point(Data start, Data end) {
            Point loc = end.location.add(end.velocity, -1);
            Vector v1 = start.location.sub(loc).relative(start.velocity.d);
            if (!isValidVelocityChange(start.velocity.m, v1.m)) {
                if (isOnWall(loc) || isOnWall(end.location) && end.velocity.m == 0.0) {
                    List<Data> sim1 = simulate(start, 2, (d, c) -> {
                        if (d.time == start.time) {
                            c.distanceRemaining = start.velocity.m < 0.0 ? Double.NEGATIVE_INFINITY : Double.POSITIVE_INFINITY;
                        } else if (d.time == start.time + 1) {
                            c.distanceRemaining = end.velocity.m < 0.0 ? Double.NEGATIVE_INFINITY : Double.POSITIVE_INFINITY;
                            c.bodyTurnRemaining = normalRelativeAngle(end.velocity.d - d.velocity.d);
                        }
                    });
                    List<Data> sim2 = simulate(start, 2, (d, c) -> {
                        if (d.time == start.time) {
                            c.distanceRemaining = start.velocity.m < 0.0 ? Double.NEGATIVE_INFINITY : Double.POSITIVE_INFINITY;
                            c.bodyTurnRemaining = normalRelativeAngle(end.velocity.d - d.velocity.d);
                        } else if (d.time == start.time + 1) {
                            c.distanceRemaining = end.velocity.m < 0.0 ? Double.NEGATIVE_INFINITY : Double.POSITIVE_INFINITY;
                        }
                    });
                    Data last1 = sim1.get(sim1.size() - 1);
                    double d1 = distance(last1, end);
                    Data last2 = sim2.get(sim2.size() - 1);
                    double d2 = distance(last2, end);
                    List<Data> sim = d1 < d2 ? sim1 : sim2;
                    Data last = d1 < d2 ? last1 : last2;
                    double d = d1 < d2 ? d1 : d2;
                    if (d < SIM_DELTA) {
                        return replaceLast(sim, last.hitWall != null ? end.hitWall(last.hitWall) : end);
                    } else {
                        return null;
                    }
                }
                if (end.velocity.m == 0.0) {

                }
            }
            Data sim = new Data(start.time + 1, loc, v1);
            return Arrays.asList(start, sim, end);
        }

        private static List<Data> interpolate0Point(Data start, Data end) {
            return Arrays.asList(start, end);
        }

        private static double getRelativeVelocityChange(double m0, double m1) {
            return (m1 == 0.0 ? - abs(m0) : (m1 - m0) * Math.signum(m1));
        }

        private static boolean isValidVelocityChange(double m0, double m1) {
            double dv = getRelativeVelocityChange(m0, m1);
            if (dv < -Rules.DECELERATION - NEAR_DELTA) {
                return false;
            }
            if (dv < Rules.ACCELERATION + NEAR_DELTA) {
                return true;
            }
            double maxDv = getNewVelocity(-abs(m0), Double.POSITIVE_INFINITY, Rules.MAX_VELOCITY);
            return abs(m1) < maxDv + NEAR_DELTA;
        }

        private static double getVelocityAfter(long time, double v0, double dist) {
            double cd = dist;
            double cv = v0;
            for (long t = 0; t < time; t++) {
                cv = getNewVelocity(cv, cd, Rules.MAX_VELOCITY);
                cd = Math.max(cd - cv, 0.0);
            }
            return cv;
        }

        private static double solve(DoubleUnaryOperator func, double min, double max) {
            try {
                return new BrentSolver().solve(Integer.MAX_VALUE, func::applyAsDouble, min, max);
            } catch (Exception e) {
                return Double.NaN;
            }
        }

        /*

        static class VelocityChange {
            double orgDistanceRemaining;
            double newDistanceRemaining;
            double maxVelocity = Rules.MAX_VELOCITY;
            long commandTick;
        }

        public static VelocityChange getVelocityChange(Data start, Data end) {
            long deltaTime = end.time - start.time;
            double sv = start.velocity.m;
            double ev = end.velocity.m;
            if (ev < 0 || ev == 0.0 && sv < 0.0) {
                sv = -sv;
                ev = -ev;
            }
            if (ev == sv && isNear(start.location.sub(end.location).m, deltaTime * sv)) {
                VelocityChange vc = new VelocityChange();
                vc.orgDistanceRemaining = 100.0 * signum(start.velocity.m);
                vc.newDistanceRemaining = vc.orgDistanceRemaining;
                vc.maxVelocity = sv;
                vc.commandTick = -1;
                return vc;
            }
            if (ev > sv || ev == Rules.MAX_VELOCITY) {
                double cv = sv;
                for (long t = 0; t < deltaTime; t++) {
                    cv = getNewVelocity(cv, 100.0, Rules.MAX_VELOCITY);
                    if (isNear(cv, ev)) {
                        if (t == deltaTime - 1 || sv == Rules.MAX_VELOCITY) {
                            VelocityChange vc = new VelocityChange();
                            vc.orgDistanceRemaining = 100.0 * signum(start.velocity.m);
                            vc.newDistanceRemaining = vc.orgDistanceRemaining;
                            vc.commandTick = -1;
                            return vc;
                        } else if (isNear(sv, 0.0)) {
                            VelocityChange vc = new VelocityChange();
                            vc.orgDistanceRemaining = 0.0;
                            vc.newDistanceRemaining = 100.0 * signum(end.velocity.m);
                            vc.commandTick = start.time + deltaTime - 1 - t;
                            return vc;
                        }
                    }
                }
                if (cv < ev) {
                    return null;
                }
            }
            if (ev < sv || ev == 0.0) {
                double cv = sv;
                for (long t = 0; t < deltaTime; t++) {
                    cv = getNewVelocity(cv, 0.0, Rules.MAX_VELOCITY);
                    if (isNear(cv, ev)) {
                        if (isNear(sv, 0.0)) {
                            VelocityChange vc = new VelocityChange();
                            vc.orgDistanceRemaining = 0.0;
                            vc.newDistanceRemaining = vc.orgDistanceRemaining;
                            vc.commandTick = -1;
                            return vc;
                        } else if (isNear(sv, Rules.MAX_VELOCITY)) {
                            VelocityChange vc = new VelocityChange();
                            vc.orgDistanceRemaining = 100.0 * signum(start.velocity.m);
                            vc.newDistanceRemaining = 0.0 * signum(end.velocity.m);
                            vc.commandTick = start.time + deltaTime - 1 - t;
                            return vc;
                        }
                    }
                }
                if (cv > ev) {
                    return null;
                }
            }
            if (sv < 0.0) {
                long t = start.time;
                double cv = sv;
                while (cv > 0) {
                    cv = getNewVelocity(cv, 0.0, Rules.MAX_VELOCITY);
                    t++;
                }
            }

            double dl = 0.0;
            double dh = Rules.MAX_VELOCITY * deltaTime;
            while (dh - dl >= DELTA) {
                double cv = sv;
                double d = (dh + dl) / 2.0;
                double cd = d;
                for (long t = 0; t < deltaTime; t++) {
                    cv = getNewVelocity(cv, cd, Rules.MAX_VELOCITY);
                    cd -= cv;
                }
                if (isNear(cv, ev)) {
                    VelocityChange vc = new VelocityChange();
                    vc.orgDistanceRemaining = d * signum(end.velocity.m);
                    vc.newDistanceRemaining = d * signum(end.velocity.m);
                    vc.commandTick = -1;
                    return vc;
                } else if (cv > ev) {
                    dh = d;
                } else {
                    dl = d;
                }
            }
            return null;
        }
        */

        private static double distance(Data d0, Data d1) {
            return sq(d0.location.x - d1.location.x)
                    + sq(d0.location.y - d1.location.y)
                    + sq(d0.velocity.dx - d1.velocity.dx)
                    + sq(d0.velocity.dy - d1.velocity.dy);
        }

        private static double sq(double a) {
            return a * a;
        }

        public static List<Data> simulate(Data start, long deltaTime,
                                          BiConsumer<Data, Command> driver) {
            return simulate(start, new BiPredicate<Data, Command>() {
                long delta = deltaTime;
                @Override
                public boolean test(Data data, Command command) {
                    driver.accept(data, command);
                    return --delta > 0;
                }
            });
        }

        public static List<Data> simulate(Data start, BiPredicate<Data, Command> driver) {
            List<Data> datas = new ArrayList<>();
            datas.add(start);

            double halfWidth = ROBOT_SIZE / 2.0;
            double minX = halfWidth;
            double minY = halfWidth;
            double maxX = battleFieldWidth - halfWidth;
            double maxY = battleFieldHeight - halfWidth;
            double x = start.location.x;
            double y = start.location.y;
            double heading = start.velocity.d;
            double velocity = start.velocity.m;
            boolean isOverDriving = false;
            Command command = new Command();
            Data cur = start;
            while (driver.test(cur, command)) {
                // updateHeading
                boolean normalizeHeading = true;
                double turnRate = min(command.maxTurnRate, (.4 + .6 * (1 - (abs(velocity) / Rules.MAX_VELOCITY))) * Rules.MAX_TURN_RATE_RADIANS);
                if (command.bodyTurnRemaining > 0) {
                    if (command.bodyTurnRemaining < turnRate) {
                        heading += command.bodyTurnRemaining;
                        command.bodyTurnRemaining = 0;
                    } else {
                        heading += turnRate;
                        command.bodyTurnRemaining -= turnRate;
                    }
                } else if (command.bodyTurnRemaining < 0) {
                    if (command.bodyTurnRemaining > -turnRate) {
                        heading += command.bodyTurnRemaining;
                        command.bodyTurnRemaining = 0;
                    } else {
                        heading -= turnRate;
                        command.bodyTurnRemaining += turnRate;
                    }
                } else {
                    normalizeHeading = false;
                }
                if (normalizeHeading) {
                    if (command.bodyTurnRemaining == 0.0) {
                        heading = Utils.normalNearAbsoluteAngle(heading);
                    } else {
                        heading = Utils.normalAbsoluteAngle(heading);
                    }
                }

                // updateMovement
                double distance = command.distanceRemaining;
                if (Double.isNaN(distance)) {
                    distance = 0;
                }
                velocity = getNewVelocity(velocity, distance, command.maxVelocity);
                if (isNear(velocity, 0) && isOverDriving) {
                    command.distanceRemaining = 0;
                    distance = 0;
                    isOverDriving = false;
                }
                if (signum(distance * velocity) != -1) {
                    isOverDriving = getDistanceTraveledUntilStop(velocity, command.maxVelocity) > abs(distance);
                }
                command.distanceRemaining = distance - velocity;
                if (velocity != 0) {
                    x += velocity * sin(heading);
                    y += velocity * cos(heading);
                }

                // check wall collisions
                boolean hitWall = false;
                if (x < minX || x > maxX || y < minY || y > maxY) {
                    double adjustX = 0, adjustY = 0;
                    if (x < minX) {
                        adjustX = minX - x;
                    } else if (x > maxX) {
                        adjustX = maxX - x;
                    } else if (y < minY) {
                        adjustY = minY - y;
                    } else if (y > maxY) {
                        adjustY = maxY - y;
                    }
                    if ((heading % (Math.PI / 2)) != 0) {
                        double tanHeading = tan(heading);
                        if (adjustX == 0) {
                            adjustX = adjustY * tanHeading;
                        }  else if (adjustY == 0) {
                            adjustY = adjustX / tanHeading;
                        } else if (abs(adjustX / tanHeading) > abs(adjustY)) {
                            adjustY = adjustX / tanHeading;
                        } else if (abs(adjustY * tanHeading) > abs(adjustX)) {
                            adjustX = adjustY * tanHeading;
                        }
                    }
                    x = Math.max(minX, min(maxX, x + adjustX));
                    y = Math.max(minY, min(maxY, y + adjustY));
                    command.distanceRemaining = 0.0;
                    velocity = 0;
                    hitWall = true;
                    // if (!datas.isEmpty()) {
                    //     Point prev = datas.get(datas.size() - 1).location;
                    //     if (Precision.equals(prev.distance(Point.fromXY(x, y)), 0.0d)) {
                    //         break;
                    //     }
                    // }
                }
                cur = new Data(cur.time + 1, Point.fromXY(x, y), Vector.fromDM(heading, velocity)).hitWall(hitWall);
                datas.add(cur);
            }
            return datas;
        }


        /*
        public static List<Data> simulate(Data start, long timeChange,
                                          long deltaTime,
                                          double turn, double ahead,
                                          double newTurn, double newAhead,
                                          double newMaxVelocity) {
            List<Data> datas = new ArrayList<>();
            datas.add(start);

            double x = start.location.x;
            double y = start.location.y;
            double heading = start.velocity.d;
            double velocity = start.velocity.m;
            double maxVelocity = 8.0;
            double distanceRemaining = ahead;
            double angleToTurn = turn;
            boolean isOverDriving = false;
            double maxTurnRate = Rules.MAX_TURN_RATE_RADIANS;

            for (long t = 0; t < deltaTime; t++) {
                if (t == timeChange) {
                    angleToTurn = newTurn;
                    maxVelocity = newMaxVelocity;
                    distanceRemaining = newAhead;
                }
                // updateHeading
                boolean normalizeHeading = true;
                double turnRate = min(maxTurnRate, (.4 + .6 * (1 - (abs(velocity) / Rules.MAX_VELOCITY))) * Rules.MAX_TURN_RATE_RADIANS);
                if (angleToTurn > 0) {
                    if (angleToTurn < turnRate) {
                        heading += angleToTurn;
                        angleToTurn = 0;
                    } else {
                        heading += turnRate;
                        angleToTurn -= turnRate;
                    }
                } else if (angleToTurn < 0) {
                    if (angleToTurn > -turnRate) {
                        heading += angleToTurn;
                        angleToTurn = 0;
                    } else {
                        heading -= turnRate;
                        angleToTurn += turnRate;
                    }
                } else {
                    normalizeHeading = false;
                }
                if (normalizeHeading) {
                    if (angleToTurn == 0.0) {
                        heading = Utils.normalNearAbsoluteAngle(heading);
                    } else {
                        heading = Utils.normalAbsoluteAngle(heading);
                    }
                }

                // additional check
                if (distanceRemaining == 0 && velocity == 0) {
                    datas.add(new Data(start.time + deltaTime, Point.fromXY(x, y), Vector.fromDM(heading, velocity)));
                    break;
                }

                // updateMovement
                double distance = distanceRemaining;
                if (Double.isNaN(distance)) {
                    distance = 0;
                }
                velocity = getNewVelocity(velocity, distance, maxVelocity);
                if (isNear(velocity, 0) && isOverDriving) {
                    distanceRemaining = 0;
                    distance = 0;
                    isOverDriving = false;
                }
                if (signum(distance * velocity) != -1) {
                    if (getDistanceTraveledUntilStop(velocity, maxVelocity) > abs(distance)) {
                        isOverDriving = true;
                    } else {
                        isOverDriving = false;
                    }
                }
                distanceRemaining = distance - velocity;
                if (velocity != 0) {
                    x += velocity * sin(heading);
                    y += velocity * cos(heading);
                }
                datas.add(new Data(start.time + t + 1, Point.fromXY(x, y), Vector.fromDM(heading, velocity)));
            }
            return datas;
        }
        */

        public static boolean isNear(double d0, double d1) {
            return abs(d0 - d1) <= NEAR_DELTA;
        }

        private static double getDistanceTraveledUntilStop(double velocity, double maxVelocity) {
            double distance = 0;
            velocity = abs(velocity);
            while (velocity > 0) {
                distance += (velocity = getNewVelocity(velocity, 0, maxVelocity));
            }
            return distance;
        }

        /**
         * Returns the new velocity based on the current velocity and distance to move.
         *
         * @param velocity the current velocity
         * @param distance the distance to move
         * @return the new velocity based on the current velocity and distance to move
         *
         * This is Patrick Cupka (aka Voidious), Julian Kent (aka Skilgannon), and Positive's method described here:
         *   http://robowiki.net/wiki/User:Voidious/Optimal_Velocity#Hijack_2
         */
        private static double getNewVelocity(double velocity, double distance, double maxVelocity) {
            if (distance < 0) {
                // If the distance is negative, then change it to be positive
                // and change the sign of the input velocity and the result
                return -getNewVelocity(-velocity, -distance, maxVelocity);
            }

            final double goalVel;

            if (distance == Double.POSITIVE_INFINITY) {
                goalVel = maxVelocity;
            } else {
                goalVel = min(getMaxVelocity(distance), maxVelocity);
            }

            if (velocity >= 0) {
                return Math.max(velocity - Rules.DECELERATION, min(goalVel, velocity + Rules.ACCELERATION));
            }
            // else
            return Math.max(velocity - Rules.ACCELERATION, min(goalVel, velocity + maxDecel(-velocity)));
        }

        private static double getMaxVelocity(double distance) {
            final double decelTime = Math.max(1, ceil(// sum of 0... decelTime, solving for decelTime using quadratic formula
                    (sqrt((4 * 2 / Rules.DECELERATION) * distance + 1) - 1) / 2));

            if (decelTime == Double.POSITIVE_INFINITY) {
                return Rules.MAX_VELOCITY;
            }

            final double decelDist = (decelTime / 2.0) * (decelTime - 1) // sum of 0..(decelTime-1)
                    * Rules.DECELERATION;

            return ((decelTime - 1) * Rules.DECELERATION) + ((distance - decelDist) / decelTime);
        }

        private static double maxDecel(double speed) {
            double decelTime = speed / Rules.DECELERATION;
            double accelTime = (1 - decelTime);

            return min(1, decelTime) * Rules.DECELERATION + Math.max(0, accelTime) * Rules.ACCELERATION;
        }

    }

    public static class Point {

        public final double x, y;

        private Point(double x, double y) {
            this.x = x;
            this.y = y;
        }

        public static Point fromXY(double x, double y) {
            return new Point(x, y);
        }

        public double angleTo(Point other) {
            return normalAbsoluteAngle(atan2(other.x - x, other.y - y));
        }

        public double distance(Point other) {
            return hypot(other.x - x, other.y - y);
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
            return String.format("Point{x=%.2f, y=%.2f}", x, y);
        }

        public double lineDist(Point p1, Point p2) {
            return abs((p2.y - p1.y) * x - (p2.x - p1.x) * y + p2.x * p1.y - p2.y * p1.x) / p1.distance(p2);
        }
    }

    /**
     * Utilities for comparing numbers.
     *
     * @since 3.0
     */
    public static class Precision {
        /**
         * <p>
         * Largest double-precision floating-point number such that
         * {@code 1 + EPSILON} is numerically equal to 1. This value is an upper
         * bound on the relative error due to rounding real numbers to double
         * precision floating-point numbers.
         * </p>
         * <p>
         * In IEEE 754 arithmetic, this is 2<sup>-53</sup>.
         * </p>
         *
         * @see <a href="http://en.wikipedia.org/wiki/Machine_epsilon">Machine epsilon</a>
         */
        public static final double EPSILON;

        /**
         * Safe minimum, such that {@code 1 / SAFE_MIN} does not overflow.
         * <p>
         * In IEEE 754 arithmetic, this is also the smallest normalized
         * number 2<sup>-1022</sup>.
         */
        public static final double SAFE_MIN;

        /** Exponent offset in IEEE754 representation. */
        private static final long EXPONENT_OFFSET = 1023l;

        /** Offset to order signed double numbers lexicographically. */
        private static final long SGN_MASK = 0x8000000000000000L;
        /** Offset to order signed double numbers lexicographically. */
        private static final int SGN_MASK_FLOAT = 0x80000000;
        /** Positive zero. */
        private static final double POSITIVE_ZERO = 0d;
        /** Positive zero bits. */
        private static final long POSITIVE_ZERO_DOUBLE_BITS = Double.doubleToRawLongBits(+0.0);
        /** Negative zero bits. */
        private static final long NEGATIVE_ZERO_DOUBLE_BITS = Double.doubleToRawLongBits(-0.0);
        /** Positive zero bits. */
        private static final int POSITIVE_ZERO_FLOAT_BITS   = Float.floatToRawIntBits(+0.0f);
        /** Negative zero bits. */
        private static final int NEGATIVE_ZERO_FLOAT_BITS   = Float.floatToRawIntBits(-0.0f);

        static {
            /*
             *  This was previously expressed as = 0x1.0p-53;
             *  However, OpenJDK (Sparc Solaris) cannot handle such small
             *  constants: MATH-721
             */
            EPSILON = Double.longBitsToDouble((EXPONENT_OFFSET - 53l) << 52);

            /*
             * This was previously expressed as = 0x1.0p-1022;
             * However, OpenJDK (Sparc Solaris) cannot handle such small
             * constants: MATH-721
             */
            SAFE_MIN = Double.longBitsToDouble((EXPONENT_OFFSET - 1022l) << 52);
        }

        /**
         * Private constructor.
         */
        private Precision() {}

        /**
         * Compares two numbers given some amount of allowed error.
         *
         * @param x the first number
         * @param y the second number
         * @param eps the amount of error to allow when checking for equality
         * @return <ul><li>0 if  {@link #equals(double, double, double) equals(x, y, eps)}</li>
         *       <li>&lt; 0 if !{@link #equals(double, double, double) equals(x, y, eps)} &amp;&amp; x &lt; y</li>
         *       <li>&gt; 0 if !{@link #equals(double, double, double) equals(x, y, eps)} &amp;&amp; x &gt; y or
         *       either argument is NaN</li></ul>
         */
        public static int compareTo(double x, double y, double eps) {
            if (equals(x, y, eps)) {
                return 0;
            } else if (x < y) {
                return -1;
            }
            return 1;
        }

        /**
         * Compares two numbers given some amount of allowed error.
         * Two float numbers are considered equal if there are {@code (maxUlps - 1)}
         * (or fewer) floating point numbers between them, i.e. two adjacent floating
         * point numbers are considered equal.
         * Adapted from <a
         * href="http://randomascii.wordpress.com/2012/02/25/comparing-floating-point-numbers-2012-edition/">
         * Bruce Dawson</a>. Returns {@code false} if either of the arguments is NaN.
         *
         * @param x first value
         * @param y second value
         * @param maxUlps {@code (maxUlps - 1)} is the number of floating point
         * values between {@code x} and {@code y}.
         * @return <ul><li>0 if  {@link #equals(double, double, int) equals(x, y, maxUlps)}</li>
         *       <li>&lt; 0 if !{@link #equals(double, double, int) equals(x, y, maxUlps)} &amp;&amp; x &lt; y</li>
         *       <li>&gt; 0 if !{@link #equals(double, double, int) equals(x, y, maxUlps)} &amp;&amp; x &gt; y
         *       or either argument is NaN</li></ul>
         */
        public static int compareTo(final double x, final double y, final int maxUlps) {
            if (equals(x, y, maxUlps)) {
                return 0;
            } else if (x < y) {
                return -1;
            }
            return 1;
        }

        /**
         * Returns true iff they are equal as defined by
         * {@link #equals(float,float,int) equals(x, y, 1)}.
         *
         * @param x first value
         * @param y second value
         * @return {@code true} if the values are equal.
         */
        public static boolean equals(float x, float y) {
            return equals(x, y, 1);
        }

        /**
         * Returns true if both arguments are NaN or they are
         * equal as defined by {@link #equals(float,float) equals(x, y, 1)}.
         *
         * @param x first value
         * @param y second value
         * @return {@code true} if the values are equal or both are NaN.
         * @since 2.2
         */
        public static boolean equalsIncludingNaN(float x, float y) {
            return (x != x || y != y) ? !(x != x ^ y != y) : equals(x, y, 1);
        }

        /**
         * Returns true if the arguments are equal or within the range of allowed
         * error (inclusive).  Returns {@code false} if either of the arguments
         * is NaN.
         *
         * @param x first value
         * @param y second value
         * @param eps the amount of absolute error to allow.
         * @return {@code true} if the values are equal or within range of each other.
         * @since 2.2
         */
        public static boolean equals(float x, float y, float eps) {
            return equals(x, y, 1) || abs(y - x) <= eps;
        }

        /**
         * Returns true if the arguments are both NaN, are equal, or are within the range
         * of allowed error (inclusive).
         *
         * @param x first value
         * @param y second value
         * @param eps the amount of absolute error to allow.
         * @return {@code true} if the values are equal or within range of each other,
         * or both are NaN.
         * @since 2.2
         */
        public static boolean equalsIncludingNaN(float x, float y, float eps) {
            return equalsIncludingNaN(x, y) || (abs(y - x) <= eps);
        }

        /**
         * Returns true if the arguments are equal or within the range of allowed
         * error (inclusive).
         * Two float numbers are considered equal if there are {@code (maxUlps - 1)}
         * (or fewer) floating point numbers between them, i.e. two adjacent floating
         * point numbers are considered equal.
         * Adapted from <a
         * href="http://randomascii.wordpress.com/2012/02/25/comparing-floating-point-numbers-2012-edition/">
         * Bruce Dawson</a>.  Returns {@code false} if either of the arguments is NaN.
         *
         * @param x first value
         * @param y second value
         * @param maxUlps {@code (maxUlps - 1)} is the number of floating point
         * values between {@code x} and {@code y}.
         * @return {@code true} if there are fewer than {@code maxUlps} floating
         * point values between {@code x} and {@code y}.
         * @since 2.2
         */
        public static boolean equals(final float x, final float y, final int maxUlps) {

            final int xInt = Float.floatToRawIntBits(x);
            final int yInt = Float.floatToRawIntBits(y);

            final boolean isEqual;
            if (((xInt ^ yInt) & SGN_MASK_FLOAT) == 0) {
                // number have same sign, there is no risk of overflow
                isEqual = abs(xInt - yInt) <= maxUlps;
            } else {
                // number have opposite signs, take care of overflow
                final int deltaPlus;
                final int deltaMinus;
                if (xInt < yInt) {
                    deltaPlus  = yInt - POSITIVE_ZERO_FLOAT_BITS;
                    deltaMinus = xInt - NEGATIVE_ZERO_FLOAT_BITS;
                } else {
                    deltaPlus  = xInt - POSITIVE_ZERO_FLOAT_BITS;
                    deltaMinus = yInt - NEGATIVE_ZERO_FLOAT_BITS;
                }

                if (deltaPlus > maxUlps) {
                    isEqual = false;
                } else {
                    isEqual = deltaMinus <= (maxUlps - deltaPlus);
                }

            }

            return isEqual && !Float.isNaN(x) && !Float.isNaN(y);

        }

        /**
         * Returns true if the arguments are both NaN or if they are equal as defined
         * by {@link #equals(float,float,int) equals(x, y, maxUlps)}.
         *
         * @param x first value
         * @param y second value
         * @param maxUlps {@code (maxUlps - 1)} is the number of floating point
         * values between {@code x} and {@code y}.
         * @return {@code true} if both arguments are NaN or if there are less than
         * {@code maxUlps} floating point values between {@code x} and {@code y}.
         * @since 2.2
         */
        public static boolean equalsIncludingNaN(float x, float y, int maxUlps) {
            return (x != x || y != y) ? !(x != x ^ y != y) : equals(x, y, maxUlps);
        }

        /**
         * Returns true iff they are equal as defined by
         * {@link #equals(double,double,int) equals(x, y, 1)}.
         *
         * @param x first value
         * @param y second value
         * @return {@code true} if the values are equal.
         */
        public static boolean equals(double x, double y) {
            return equals(x, y, 1);
        }

        /**
         * Returns true if the arguments are both NaN or they are
         * equal as defined by {@link #equals(double,double) equals(x, y, 1)}.
         *
         * @param x first value
         * @param y second value
         * @return {@code true} if the values are equal or both are NaN.
         * @since 2.2
         */
        public static boolean equalsIncludingNaN(double x, double y) {
            return (x != x || y != y) ? !(x != x ^ y != y) : equals(x, y, 1);
        }

        /**
         * Returns {@code true} if there is no double value strictly between the
         * arguments or the difference between them is within the range of allowed
         * error (inclusive). Returns {@code false} if either of the arguments
         * is NaN.
         *
         * @param x First value.
         * @param y Second value.
         * @param eps Amount of allowed absolute error.
         * @return {@code true} if the values are two adjacent floating point
         * numbers or they are within range of each other.
         */
        public static boolean equals(double x, double y, double eps) {
            return equals(x, y, 1) || abs(y - x) <= eps;
        }

        /**
         * Returns {@code true} if there is no double value strictly between the
         * arguments or the relative difference between them is less than or equal
         * to the given tolerance. Returns {@code false} if either of the arguments
         * is NaN.
         *
         * @param x First value.
         * @param y Second value.
         * @param eps Amount of allowed relative error.
         * @return {@code true} if the values are two adjacent floating point
         * numbers or they are within range of each other.
         * @since 3.1
         */
        public static boolean equalsWithRelativeTolerance(double x, double y, double eps) {
            if (equals(x, y, 1)) {
                return true;
            }

            final double absoluteMax = Math.max(abs(x), abs(y));
            final double relativeDifference = abs((x - y) / absoluteMax);

            return relativeDifference <= eps;
        }

        /**
         * Returns true if the arguments are both NaN, are equal or are within the range
         * of allowed error (inclusive).
         *
         * @param x first value
         * @param y second value
         * @param eps the amount of absolute error to allow.
         * @return {@code true} if the values are equal or within range of each other,
         * or both are NaN.
         * @since 2.2
         */
        public static boolean equalsIncludingNaN(double x, double y, double eps) {
            return equalsIncludingNaN(x, y) || (abs(y - x) <= eps);
        }

        /**
         * Returns true if the arguments are equal or within the range of allowed
         * error (inclusive).
         * <p>
         * Two float numbers are considered equal if there are {@code (maxUlps - 1)}
         * (or fewer) floating point numbers between them, i.e. two adjacent
         * floating point numbers are considered equal.
         * </p>
         * <p>
         * Adapted from <a
         * href="http://randomascii.wordpress.com/2012/02/25/comparing-floating-point-numbers-2012-edition/">
         * Bruce Dawson</a>. Returns {@code false} if either of the arguments is NaN.
         * </p>
         *
         * @param x first value
         * @param y second value
         * @param maxUlps {@code (maxUlps - 1)} is the number of floating point
         * values between {@code x} and {@code y}.
         * @return {@code true} if there are fewer than {@code maxUlps} floating
         * point values between {@code x} and {@code y}.
         */
        public static boolean equals(final double x, final double y, final int maxUlps) {

            final long xInt = Double.doubleToRawLongBits(x);
            final long yInt = Double.doubleToRawLongBits(y);

            final boolean isEqual;
            if (((xInt ^ yInt) & SGN_MASK) == 0l) {
                // number have same sign, there is no risk of overflow
                isEqual = abs(xInt - yInt) <= maxUlps;
            } else {
                // number have opposite signs, take care of overflow
                final long deltaPlus;
                final long deltaMinus;
                if (xInt < yInt) {
                    deltaPlus  = yInt - POSITIVE_ZERO_DOUBLE_BITS;
                    deltaMinus = xInt - NEGATIVE_ZERO_DOUBLE_BITS;
                } else {
                    deltaPlus  = xInt - POSITIVE_ZERO_DOUBLE_BITS;
                    deltaMinus = yInt - NEGATIVE_ZERO_DOUBLE_BITS;
                }

                if (deltaPlus > maxUlps) {
                    isEqual = false;
                } else {
                    isEqual = deltaMinus <= (maxUlps - deltaPlus);
                }

            }

            return isEqual && !Double.isNaN(x) && !Double.isNaN(y);

        }

        /**
         * Returns true if both arguments are NaN or if they are equal as defined
         * by {@link #equals(double,double,int) equals(x, y, maxUlps)}.
         *
         * @param x first value
         * @param y second value
         * @param maxUlps {@code (maxUlps - 1)} is the number of floating point
         * values between {@code x} and {@code y}.
         * @return {@code true} if both arguments are NaN or if there are less than
         * {@code maxUlps} floating point values between {@code x} and {@code y}.
         * @since 2.2
         */
        public static boolean equalsIncludingNaN(double x, double y, int maxUlps) {
            return (x != x || y != y) ? !(x != x ^ y != y) : equals(x, y, maxUlps);
        }

        /**
         * Rounds the given value to the specified number of decimal places.
         * The value is rounded using the {@link BigDecimal#ROUND_HALF_UP} method.
         *
         * @param x Value to round.
         * @param scale Number of digits to the right of the decimal point.
         * @return the rounded value.
         * @since 1.1 (previously in {@code MathUtils}, moved as of version 3.0)
         */
        public static double round(double x, int scale) {
            return round(x, scale, BigDecimal.ROUND_HALF_UP);
        }

        /**
         * Rounds the given value to the specified number of decimal places.
         * The value is rounded using the given method which is any method defined
         * in {@link BigDecimal}.
         * If {@code x} is infinite or {@code NaN}, then the value of {@code x} is
         * returned unchanged, regardless of the other parameters.
         *
         * @param x Value to round.
         * @param scale Number of digits to the right of the decimal point.
         * @param roundingMethod Rounding method as defined in {@link BigDecimal}.
         * @return the rounded value.
         * @throws ArithmeticException if {@code roundingMethod == ROUND_UNNECESSARY}
         * and the specified scaling operation would require rounding.
         * @throws IllegalArgumentException if {@code roundingMethod} does not
         * represent a valid rounding mode.
         * @since 1.1 (previously in {@code MathUtils}, moved as of version 3.0)
         */
        public static double round(double x, int scale, int roundingMethod) {
            try {
                final double rounded = (new BigDecimal(Double.toString(x))
                       .setScale(scale, roundingMethod))
                       .doubleValue();
                // MATH-1089: negative values rounded to zero should result in negative zero
                return rounded == POSITIVE_ZERO ? POSITIVE_ZERO * x : rounded;
            } catch (NumberFormatException ex) {
                if (Double.isInfinite(x)) {
                    return x;
                } else {
                    return Double.NaN;
                }
            }
        }

        /**
         * Rounds the given value to the specified number of decimal places.
         * The value is rounded using the {@link BigDecimal#ROUND_HALF_UP} method.
         *
         * @param x Value to round.
         * @param scale Number of digits to the right of the decimal point.
         * @return the rounded value.
         * @since 1.1 (previously in {@code MathUtils}, moved as of version 3.0)
         */
        public static float round(float x, int scale) {
            return round(x, scale, BigDecimal.ROUND_HALF_UP);
        }

        /**
         * Rounds the given value to the specified number of decimal places.
         * The value is rounded using the given method which is any method defined
         * in {@link BigDecimal}.
         *
         * @param x Value to round.
         * @param scale Number of digits to the right of the decimal point.
         * @param roundingMethod Rounding method as defined in {@link BigDecimal}.
         * @return the rounded value.
         * @since 1.1 (previously in {@code MathUtils}, moved as of version 3.0)
         * @throws ArithmeticException if an exact operation is required but result is not exact
         * @throws IllegalArgumentException if {@code roundingMethod} is not a valid rounding method.
         */
        public static float round(float x, int scale, int roundingMethod) {
            final float sign = copySign(1f, x);
            final float factor = (float) pow(10.0f, scale) * sign;
            return (float) roundUnscaled(x * factor, sign, roundingMethod) / factor;
        }

        /**
         * Rounds the given non-negative value to the "nearest" integer. Nearest is
         * determined by the rounding method specified. Rounding methods are defined
         * in {@link BigDecimal}.
         *
         * @param unscaled Value to round.
         * @param sign Sign of the original, scaled value.
         * @param roundingMethod Rounding method, as defined in {@link BigDecimal}.
         * @return the rounded value.
         * @throws ArithmeticException if an exact operation is required but result is not exact
         * @throws IllegalArgumentException if {@code roundingMethod} is not a valid rounding method.
         * @since 1.1 (previously in {@code MathUtils}, moved as of version 3.0)
         */
        private static double roundUnscaled(double unscaled,
                                            double sign,
                                            int roundingMethod) {
            switch (roundingMethod) {
            case BigDecimal.ROUND_CEILING :
                if (sign == -1) {
                    unscaled = floor(nextAfter(unscaled, Double.NEGATIVE_INFINITY));
                } else {
                    unscaled = ceil(nextAfter(unscaled, Double.POSITIVE_INFINITY));
                }
                break;
            case BigDecimal.ROUND_DOWN :
                unscaled = floor(nextAfter(unscaled, Double.NEGATIVE_INFINITY));
                break;
            case BigDecimal.ROUND_FLOOR :
                if (sign == -1) {
                    unscaled = ceil(nextAfter(unscaled, Double.POSITIVE_INFINITY));
                } else {
                    unscaled = floor(nextAfter(unscaled, Double.NEGATIVE_INFINITY));
                }
                break;
            case BigDecimal.ROUND_HALF_DOWN : {
                unscaled = nextAfter(unscaled, Double.NEGATIVE_INFINITY);
                double fraction = unscaled - floor(unscaled);
                if (fraction > 0.5) {
                    unscaled = ceil(unscaled);
                } else {
                    unscaled = floor(unscaled);
                }
                break;
            }
            case BigDecimal.ROUND_HALF_EVEN : {
                double fraction = unscaled - floor(unscaled);
                if (fraction > 0.5) {
                    unscaled = ceil(unscaled);
                } else if (fraction < 0.5) {
                    unscaled = floor(unscaled);
                } else {
                    // The following equality test is intentional and needed for rounding purposes
                    if (floor(unscaled) / 2.0 == floor(floor(unscaled) / 2.0)) { // even
                        unscaled = floor(unscaled);
                    } else { // odd
                        unscaled = ceil(unscaled);
                    }
                }
                break;
            }
            case BigDecimal.ROUND_HALF_UP : {
                unscaled = nextAfter(unscaled, Double.POSITIVE_INFINITY);
                double fraction = unscaled - floor(unscaled);
                if (fraction >= 0.5) {
                    unscaled = ceil(unscaled);
                } else {
                    unscaled = floor(unscaled);
                }
                break;
            }
            case BigDecimal.ROUND_UNNECESSARY :
                if (unscaled != floor(unscaled)) {
                    throw new ArithmeticException();
                }
                break;
            case BigDecimal.ROUND_UP :
                // do not round if the discarded fraction is equal to zero
                if (unscaled != floor(unscaled)) {
                    unscaled = ceil(nextAfter(unscaled, Double.POSITIVE_INFINITY));
                }
                break;
            default :
                throw new IllegalArgumentException("invalid rounding method");
            }
            return unscaled;
        }


        /**
         * Computes a number {@code delta} close to {@code originalDelta} with
         * the property that <pre><code>
         *   x + delta - x
         * </code></pre>
         * is exactly machine-representable.
         * This is useful when computing numerical derivatives, in order to reduce
         * roundoff errors.
         *
         * @param x Value.
         * @param originalDelta Offset value.
         * @return a number {@code delta} so that {@code x + delta} and {@code x}
         * differ by a representable floating number.
         */
        public static double representableDelta(double x,
                                                double originalDelta) {
            return x + originalDelta - x;
        }
    }

    public static class Rect {
        public final double x, y, w, h;

        public Rect(double x, double y, double w, double h) {
            this.x = x;
            this.y = y;
            this.w = w;
            this.h = h;
        }

        public boolean contains(Point p) {
            return p.x >= x && p.x <= x + w
                    && p.y >= y && p.y <= y + h;
        }
    }

    public static class Vector {
        public final double dx, dy, d, m;

        private Vector(double dx, double dy, double d, double m) {
            this.dx = dx;
            this.dy = dy;
            this.d = d;
            this.m = roundComputeErrors(m);
        }

        public static Vector fromDM(double dir, double mag) {
            dir = normalAbsoluteAngle(dir);
            return new Vector(mag * sin(dir), mag * cos(dir), dir, mag);
        }

        public static Vector fromXY(double dx, double dy) {
            return new Vector(dx, dy, normalAbsoluteAngle(atan2(dx, dy)), hypot(dx, dy));
        }

        public Vector relative(double dir) {
            if (abs(normalRelativeAngle(dir - d)) > PI / 2.0) {
                return Vector.fromDM(d + PI, -m);
            } else {
                return this;
            }
        }

        public Vector add(Vector v) {
            return Vector.fromXY(dx + v.dx, dy + v.dy);
        }

        public Vector scale(double scale) {
            return Vector.fromDM(d, m * scale);
        }

        @Override
        public String toString() {
            return String.format("Vector{dx=%.2f, dy=%.2f, d=%.2f, m=%.2f}", dx, dy, (d * 180 / PI), m);
        }
    }

    public static double roundComputeErrors(double value) {
        double scale1 = pow(10, 5);
        double scale2 = pow(10, 10);
        double r1 = round(value * scale1) / scale1;
        double r2 = round(value * scale2) / scale2;
        return (r1 == r2) ? r1 : value;
    }
}
