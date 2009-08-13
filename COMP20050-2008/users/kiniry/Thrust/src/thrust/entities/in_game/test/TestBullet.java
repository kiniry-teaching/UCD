/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "May 2008"
 * @keywords "C=64", "Thrust", "game"
 */
package thrust.entities.in_game.test;

import thrust.entities.in_game.Bullet;

import java.util.logging.ConsoleHandler;
import java.util.logging.Handler;
import java.util.logging.Logger;

/**
 * Test that a bullet behaves properly.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 May 2008
 */
public final class TestBullet {
  /** What unit of time is used for simulation updates? */
  private static final double TIME_INCREMENT = 0.1;
  /** How long should we run this simulation test? */
  private static final double TIME_DURATION = 10;

  /** This class cannot be created. */
  private TestBullet() {
    assert false; //@ assert false;
  }

  /**
   * Create a bullet at position (0,0) with velocity (1,0)
   * and simulate motion for 10 seconds.
   * @param the_args ignored
   */
  public static void main(final String[] the_args) {
    final double[] right_velocity = {1, 0};
    final Bullet the_bullet = new Bullet();
    final Logger my_logger = Logger.getLogger("TestBullet");
    final Handler my_handler = new ConsoleHandler();
    my_logger.addHandler(my_handler);
    my_logger.getHandlers()[0].setFormatter(new thrust.ShortFormatter());
    my_logger.setUseParentHandlers(false);
    the_bullet.velocity(right_velocity);
    my_logger.info("Created the bullet:" + the_bullet);
    my_logger.info("TIME\t\tSTATE");
    my_logger.info("====\t\t=====");
    for (double time = 0; time < TIME_DURATION; time += TIME_INCREMENT) {
      my_logger.info(time + "\t\t" + the_bullet);
      the_bullet.simulate(TIME_INCREMENT);
    }
  }
}
