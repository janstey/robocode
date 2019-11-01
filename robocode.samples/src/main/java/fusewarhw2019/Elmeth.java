package fusewarhw2019;

import java.awt.*;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.concurrent.atomic.AtomicInteger;

import fusewarhw2019.elmeth.Core;
import fusewarhw2019.elmeth.CrazyCore;
import fusewarhw2019.elmeth.SpinCore;
import fusewarhw2019.elmeth.WallsCore;
import robocode.AdvancedRobot;
import robocode.HitRobotEvent;
import robocode.HitWallEvent;
import robocode.ScannedRobotEvent;

/**
 * A robot as elegant & excellent as the mobile armour Elmeth:
 * https://gundam.fandom.com/wiki/MAN-08_Elmeth
 *
 * @author tasato
 */
public class Elmeth extends AdvancedRobot {

    private static final int INTERVAL = 1; // morph every turn

    private final Random random = new Random();
    private final List<Core> cores;
    private int counter = 0;
    private Core core;

    public Elmeth() {
        // weights (<= 100) per decision core
        cores = Arrays.asList(
            new SpinCore(this, 40),
            new WallsCore(this, 40),
            new CrazyCore(this, 20));
        System.out.println("[Elmeth] core table: " + cores);

        core = elect();
    }

    private Core elect() {
        int n = random.nextInt(100);
        AtomicInteger sum = new AtomicInteger();
        Core elected = cores.stream()
            .filter(core -> {
                sum.addAndGet(core.getWeight());
                return n < sum.get();
            })
            .findFirst()
            .get();
        System.out.println("[Elmeth] core: " + elected.getClass().getSimpleName());
        return elected;
    }

    public void run() {
        // Elmeth colors
        setBodyColor(Color.green);
        setGunColor(Color.black);
        setRadarColor(Color.blue);
        setBulletColor(Color.yellow);
        setScanColor(Color.orange);

        core.init();

        while (true) {
            doRun();
        }
    }

    private void doRun() {
        System.out.println("[Elmeth] counter = " + counter);
        core.run();
        counter++;
        if (counter % INTERVAL == 0) {
            core = elect();
            core.init();
        }
    }

    @Override
    public void onHitRobot(HitRobotEvent e) {
        core.onHitRobot(e);
    }

    @Override
    public void onScannedRobot(ScannedRobotEvent e) {
        core.onScannedRobot(e);
    }

    @Override
    public void onHitWall(HitWallEvent e) {
        core.onHitWall(e);
    }
}
