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

import java.util.Collection;
import java.util.LinkedList;
import java.util.logging.Logger;
import thrust.audio.Music;
import thrust.entities.about.GameState;
import thrust.input.KeyBoardInput;

/**
 * Simulating all of the entities in the game to realize the game.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 23 April 2008
 */
public final class Main {
  /** Game state. */
  public static final thrust.entities.about.GameState GAMESTATE =
    new thrust.entities.about.GameState();
  /** The music player. */
  public static final Music MUSIC = new Music();
  /** The input handler. */
  public static final KeyBoardInput INPUT = new KeyBoardInput();
  /** */
  public static boolean my_check = true;
  /** */
  private static Collection my_dynamics = new LinkedList();
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
    MUSIC.start();
    // wait for keyboard input
    // repeat the following until the player asks to quit
    //   show the high score display
    //   wait for input to start the game
    //   create game map and initialize location of all entities
    //   repeat the following until the player is out of lives or asks to quit:
    do {
      if (GAMESTATE.get_state() == GameState.PLAY) {
        while (GAMESTATE.lives() > 0 &&
            GAMESTATE.get_state() == GameState.PLAY) {
          my_check = true;
        }
      }
    } while(GAMESTATE.get_state() != GameState.PLAY);
    //      record the current time T
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
