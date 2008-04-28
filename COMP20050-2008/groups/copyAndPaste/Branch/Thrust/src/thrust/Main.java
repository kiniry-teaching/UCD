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

import java.util.Scanner;
import java.util.logging.Logger;
import java.util.logging.Level;
import java.io.IOException;
import javax.sound.sampled.LineUnavailableException;
import javax.sound.sampled.UnsupportedAudioFileException;
import thrust.audio.Music;
import thrust.input.InputHandler;
import thrust.entities.about.GameState;
/**
 * Simulating all of the entities in the game to realize the game.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 23 April 2008
 * @revised patirck nevin (patrick.nevin@ucdconnect.ie) 28-April-08
 */
public final class Main {
  /**
   * create a log of what to do.
   */
  private static Logger my_log = Logger.getLogger("thrust.Main");
  /**
   * This class cannot be constructed.
   */
  private Main() {
    assert false; //@ assert false;
  }
  /**
   * Run the game.
   * @param the_args The command-line arguments are ignored.
   */
  public static void main(final String[] the_args) {
    // play title music
    try {
      final Music my_music = new Music();
      my_music.start();
    } catch (LineUnavailableException e) {
      my_log.log(Level.SEVERE, "Uncaught exception", e);
    } catch (IOException i) {
      my_log.log(Level.SEVERE, "Uncaught exception", i);
    } catch (UnsupportedAudioFileException u) {
      my_log.log(Level.SEVERE, "Uncaught exception", u);
    }
    // display the title screen
    //record the time the game has exsisted for in millisecs.
    long start_time, stop_time, time_gone;
    // wait for keyboard input
    //grab the user input
    final Scanner user_input = new Scanner(System.in);
    //cast the input to a char
    char ch = user_input.next().charAt(0);
    //create a new instance of InputHandler
    InputHandler key_handler;
    //create a new instance of GameState
    final GameState the_game = new GameState();
    //start recording time
    start_time = -System.currentTimeMillis();
    while (ch != InputHandler.STOP_GAME) {
      //keep getting the users input
      ch = user_input.next().charAt(0);
      //create new instance of InputHandler to deal with input
      key_handler = new InputHandler();
      //now process the keyboard input
      key_handler.process(ch);

      // repeat the following until the player asks to quit
      while (key_handler.get_game_on()) {
      //   show the high score display
      //   wait for input to start the game
      //   create game map and initialize location of all entities
      //repeat the following until the player is out of lives or asks to quit:
        while (the_game.lives() > 0) {

          stop_time = System.currentTimeMillis();
          time_gone = start_time + stop_time;
    //      record the current time T
    //      perform a step in the simulation
    //      render all entities
    //      process the next keyboard input
    //      record the current time T'
          /**
           * thought you said not to use threads??
           */
          try {
            Thread.sleep(1000 / 30);
          } catch (InterruptedException ie) {
            my_log.log(Level.SEVERE, "Uncaught exception", ie);
          }
    //      wait for (1/30th of a second - (T-T'))
    //   remove the game interface
    //   if the player has a new high score
    //     ask them to input their initials
    //     save the new high score
        } //end while
      } //end second while
    } //end outer while
  } //end main()
} // end class
