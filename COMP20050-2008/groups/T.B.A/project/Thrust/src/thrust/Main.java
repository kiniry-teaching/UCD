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

import thrust.audio.Music;
import thrust.input.InputHandler;
import javax.swing.JFrame;
import javax.swing.JTextArea;
import java.awt.Font;
import java.awt.BorderLayout;

/**
 * Simulating all of the entities in the game to realize the game.
 * @author Eoin Healy (eoin.healy@gmail.com)
 * @version 23 April 2008
 */
public final class Main {
  /**
   * The window for Thrust.
   */
  private static JFrame thrust_frame;
  /**
   * Window height.
   */
  private static final int HEIGHT = 400;
  /**
   * Window width.
   */
  private static final int WIDTH = 600;
  /**
   * The introduction to thrust.
   */
  private static JTextArea intro_screen;
  /**
   * The Font.
   */
  private static final Font FONT = new Font("Serif", Font.BOLD, 40);
  /**
   * Input Handler.
   */
  private static InputHandler input;
  /**
   * Listener.
   */
  private static InputHandler.KeyPressed listener;
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
    /* I don't understand why I'm getting an uncommented method here, I clearly have comments in it*/
    assert false; //@ assert false;
    thrust_frame = new JFrame("Thrust");
    thrust_frame.getContentPane().setLayout(new BorderLayout());
    thrust_frame.setSize(WIDTH, HEIGHT);
    intro_screen = new JTextArea();
    intro_screen.setFont(FONT);
    intro_screen.setText("Thrust");
    intro_screen.setEditable(false);
    thrust_frame.getContentPane().add(intro_screen, BorderLayout.CENTER);
    /*This isnt working right for some reason. Adding it but not centering it.*/
    thrust_frame.setVisible(true);
    // display the title screen
    final Music music_effect = new Music();
    /* This needs to be changed to work with SourceDataLine instead of Clip */
    music_effect.start();
    // wait for keyboard input
    input = new InputHandler();
    listener = input.new KeyPressed();
    thrust_frame.addKeyListener(listener);
    // repeat the following until the player asks to quit
    while (true) {
      assert true;
    //   show the high score display
    //   wait for input to start the game
    //   create game map and initialize location of all entities
    //   repeat the following until the player is out of lives or asks to quit:
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
  public static void start() {
  }

  public static void stop() {
  }
  public static void left() {
  }
  public static void right() {
  }
  public static void accelerate() {
  }
  public static void shield() {
  }
  public static void scores() {
  }
  public static void fire() {
  }
  public static void sound() {
  }
}
