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

import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.util.logging.ConsoleHandler;
import java.util.logging.Handler;
import java.util.logging.Logger;
import thrust.audio.Music;
import thrust.input.InputHandler;
import javax.swing.JFrame;

/**
 * Simulating all of the entities in the game to realize the game.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 23 April 2008
 */
public final class Main {
  /** A logger for use by the game as a console. */
  public static final /*@ non_null @*/ Logger LOGGER =
    Logger.getLogger("Thrust");

  /** All log messages go to the console. */
  public static final /*@ non_null @*/ Handler HANDLER =
    new ConsoleHandler();

  /** To handle all input to the game. */
  public static final /*@ non_null @*/ InputHandler INPUT_HANDLER =
    new InputHandler();

  /** The frame into which we render the game. */
  public static final /*@ non_null @*/ JFrame FRAME =
    new JFrame("Thrust");

  /**
   * Create GUI for game.
   * @param the_main an instance of the main class of the game.
   */
  private static void create_gui(final /*@ non_null @*/ Main the_main) {
    // setup display
    FRAME.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
    FRAME.addKeyListener(the_main);
    FRAME.pack();
    FRAME.setVisible(true);
  }

  /** Show the game's title screen. */
  private static void display_title_screen() {
    // display the title screen
    LOGGER.info("The title screen is displayed.");
  }

  /** Play the game's title music. */
  private static void play_title_music() {
    // play title music
    final Music game_music = new Music("media/music.mp3");
    game_music.start();
  }

  /**
   * Run the game.
   * @param the_args The command-line arguments are ignored.
   */
  public static void main(final String[] the_args) {
  //Schedule a job for the event-dispatching thread:
    //creating and showing this application's GUI.
    javax.swing.SwingUtilities.invokeLater(new Runnable() {
      public void run() {
        create_gui(new Main());
        display_title_screen();
        play_title_music();
        // now the KeyListener does all the work
      }
    });
  }
}
