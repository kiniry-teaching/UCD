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

import java.util.logging.ConsoleHandler;
import java.util.logging.Handler;
import java.util.logging.Logger;
import java.util.Formatter;

/**
 * Test framework for entities.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 May 2008
 */
public class EntityTester {
  /** What unit of time is used for simulation updates? */
  public static final double TIME_INCREMENT = 0.1;
  /** How long should we run this simulation test? */
  public static final double TIME_DURATION = 10;

  /** A logger for use by all entity testers. */
  protected static final /*@ non_null @*/ Logger LOGGER =
    Logger.getLogger("EntityTester");

  /** All log messages go to the console. */
  protected static final /*@ non_null @*/ Handler HANDLER =
    new ConsoleHandler();

  /** A formatter for printing floats in an easy-to-read fashion. */
  protected static Formatter my_formatter;

  /** A protected constructor to prevent external creation. */
  protected EntityTester() {
    assert false; //@ assert false;
  }

  /** Initialize the system logger. */
  protected static void init() {
    HANDLER.setFormatter(new thrust.ShortFormatter());
    LOGGER.addHandler(HANDLER);
    LOGGER.setUseParentHandlers(false);
  }
}
