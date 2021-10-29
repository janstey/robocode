package warhw2021.gn;

import static warhw2021.gn.Utils.roundComputeErrors;

public class Data {

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
