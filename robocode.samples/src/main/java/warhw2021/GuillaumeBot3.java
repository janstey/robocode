package warhw2021;


import java.awt.*;
import java.awt.event.KeyEvent;
import java.awt.geom.Arc2D;
import java.awt.geom.Line2D;
import java.awt.geom.Rectangle2D;
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
import java.util.function.BiConsumer;
import java.util.function.Function;
import java.util.function.ToDoubleFunction;
import java.util.stream.Collectors;
import java.util.stream.DoubleStream;
import java.util.stream.IntStream;
import java.util.stream.LongStream;
import java.util.stream.Stream;

import warhw2021.gn.Data;
import warhw2021.gn.KDTree;
import warhw2021.gn.MovementInterpolator;
import warhw2021.gn.Point;
import warhw2021.gn.Rect;
import warhw2021.gn.Vector;
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

import static warhw2021.gn.Utils.roundComputeErrors;
import static robocode.util.Utils.isNear;


/**
 * GuillaumeBot
 *
 * @author Guillaume Nodet (original)
 */
public class GuillaumeBot3 extends AdvancedRobot {

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
                        if (cluster.size() > 0) {
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
            return GuillaumeBot3.getMoveTree(this.name, name);
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
        final GuillaumeBot3 actor;
        final Robots robots;
        boolean paint = true;
        double prevHeading = Double.NaN;
        double pprevHeading = Double.NaN;
        double ppprevHeading = Double.NaN;

        public BaseRadar(GuillaumeBot3 actor, Robots robots) {
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

        public MeleeRadar(GuillaumeBot3 actor, Robots robots) {
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
        MAX_X = MovementInterpolator.battleFieldHeight = getBattleFieldHeight();
        MAX_Y = MovementInterpolator.battleFieldWidth = getBattleFieldWidth();
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

}
