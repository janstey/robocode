package warhw2021.gn;

public class Rect {
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
