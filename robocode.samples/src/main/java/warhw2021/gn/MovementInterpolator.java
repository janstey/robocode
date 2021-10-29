package warhw2021.gn;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.BiConsumer;
import java.util.function.BiPredicate;
import java.util.function.DoubleUnaryOperator;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import gn.maths.BrentSolver;
import robocode.Rules;
import robocode.util.Utils;

import static java.lang.Math.PI;
import static java.lang.Math.abs;
import static java.lang.Math.ceil;
import static java.lang.Math.cos;
import static java.lang.Math.floor;
import static java.lang.Math.max;
import static java.lang.Math.min;
import static java.lang.Math.signum;
import static java.lang.Math.sin;
import static java.lang.Math.sqrt;
import static java.lang.Math.tan;
import static robocode.util.Utils.normalRelativeAngle;


public class MovementInterpolator {

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
                } else if (am3 == max(am0 - deltaTime * Rules.DECELERATION, 0.0)) {
                    double am1 = max(am0 - Rules.DECELERATION, 0.0);
                    m1 = am1 * sm0;
                    m2 = max(am1 - Rules.DECELERATION, 0.0) * sm0;
                } else if (am0 == Rules.MAX_VELOCITY && am3 == Rules.MAX_VELOCITY - Rules.DECELERATION) {
                    m1 = m0;
                    m2 = m0;
                } else if (am0 == Rules.MAX_VELOCITY && am3 == Rules.MAX_VELOCITY - 2 * Rules.DECELERATION) {
                    m1 = m0;
                    m2 = max(am0 - Rules.DECELERATION, 0.0) * sm0;
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
            cd = max(cd - cv, 0.0);
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
                x = max(minX, min(maxX, x + adjustX));
                y = max(minY, min(maxY, y + adjustY));
                command.distanceRemaining = 0.0;
                velocity = 0;
                hitWall = true;
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
            return max(velocity - Rules.DECELERATION, min(goalVel, velocity + Rules.ACCELERATION));
        }
        // else
        return max(velocity - Rules.ACCELERATION, min(goalVel, velocity + maxDecel(-velocity)));
    }

    private static double getMaxVelocity(double distance) {
        final double decelTime = max(1, ceil(// sum of 0... decelTime, solving for decelTime using quadratic formula
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

        return min(1, decelTime) * Rules.DECELERATION + max(0, accelTime) * Rules.ACCELERATION;
    }

}
