package warhw2021.gn;

import static warhw2021.gn.Utils.roundComputeErrors;
import static robocode.util.Utils.normalAbsoluteAngle;
import static robocode.util.Utils.normalRelativeAngle;

public class Vector {
    public final double dx, dy, d, m;

    private Vector(double dx, double dy, double d, double m) {
        this.dx = dx;
        this.dy = dy;
        this.d = d;
        this.m = roundComputeErrors(m);
    }

    public static Vector fromDM(double dir, double mag) {
        dir = normalAbsoluteAngle(dir);
        return new Vector(mag * Math.sin(dir), mag * Math.cos(dir), dir, mag);
    }

    public static Vector fromXY(double dx, double dy) {
        return new Vector(dx, dy, normalAbsoluteAngle(Math.atan2(dx, dy)), Math.hypot(dx, dy));
    }

    public Vector relative(double dir) {
        if (Math.abs(normalRelativeAngle(dir - d)) > Math.PI / 2.0) {
            return Vector.fromDM(d + Math.PI, -m);
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
        return String.format("Vector{dx=%.2f, dy=%.2f, d=%.2f, m=%.2f}", dx, dy, (d * 180 / Math.PI), m);
    }
}
