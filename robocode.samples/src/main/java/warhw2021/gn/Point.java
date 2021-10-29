package warhw2021.gn;

import static robocode.util.Utils.normalAbsoluteAngle;

public class Point {

    public final double x, y;

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
        return String.format("Point{x=%.2f, y=%.2f}", x, y);
    }

    public double lineDist(Point p1, Point p2) {
        return Math.abs((p2.y - p1.y) * x - (p2.x - p1.x) * y + p2.x * p1.y - p2.y * p1.x) / p1.distance(p2);
    }
}
