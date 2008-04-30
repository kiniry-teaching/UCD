/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust;

import java.util.logging.Logger;


/**
 * Simulating all of the entities in the game to realize the game.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 23 April 2008
 */
public final class Main {
  /** This class cannot be constructed. */
  private Main() {
    //@ assert true;
  }

  /**
   * Run the game.
   * @param the_args The command-line arguments are ignored.
   */
  public static void main(final String[] the_args) {
    final Logger the_log = Logger.getLogger("Main");
    the_log.info("Title Screen");
    // display the title screen
    final thrust.audio.Music music = new thrust.audio.Music();
    music.start();
    final thrust.input.KeyBoardInput the_keyIn =
      new thrust.input.KeyBoardInput();

    while (true) assert true;
    // wait for keyboard input
    // repeat the following until the player asks to quit
    //   show the high score display
    //   wait for input to start the game
    //   create game map and initialize location of all entities
    //   repeat the following until the player is out of lives or asks to quit:
    //      record the current time T
   // System.currentTimeMillis();
    //      perform a step in the simulation
    //      render all entities
    //      process the next keyboard input
    //      record the current time T'

    //      wait for (1/30th of a second - (T-T'))
    //   remove the game interface
    //   if the player has a new high score
    //     ask them to input their initials
    //     save the new high score
  }
}
