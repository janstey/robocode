package warhw2021.gn;

public class Utils {

    public static double roundComputeErrors(double value) {
        double scale1 = Math.pow(10, 5);
        double scale2 = Math.pow(10, 10);
        double r1 = Math.round(value * scale1) / scale1;
        double r2 = Math.round(value * scale2) / scale2;
        return (r1 == r2) ? r1 : value;
    }

}
