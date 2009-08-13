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

import java.util.Formatter;

import thrust.entities.in_game.Spaceship;

/**
 * Test that a spaceship behaves properly.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 May 2008
 */
public final class TestSpaceship extends EntityTester {
  /** A private constructor to prevent external creation. */
  private TestSpaceship() {
    super();
    assert false; //@ assert false;
  }

  /**
   * Create a spaceship at position (0,0) with velocity (1,0)
   * and simulate motion for 10 seconds.
   * @param the_args ignored
   */
  public static void main(final String[] the_args) {
    init();
    final double[] right_velocity = {1, 0};
    final Spaceship the_spaceship = new Spaceship();
    the_spaceship.velocity(right_velocity);
    LOGGER.info("Created the spaceship: " + the_spaceship);
    LOGGER.info("TIME\t\tSTATE");
    LOGGER.info("====\t\t=====");
    for (double time = 0; time < TIME_DURATION; time += TIME_INCREMENT) {
      my_formatter = new Formatter(new StringBuilder());
      LOGGER.info(my_formatter.format("%-5.2f", time) + "\t\t" +
                  the_spaceship);
      the_spaceship.simulate(TIME_INCREMENT);
    }
  }
}
