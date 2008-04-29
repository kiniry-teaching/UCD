/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.input;
import java.awt.event.KeyEvent;

/**
 * Processes and delegates each keyboard input received.
 * @author Siobhán Dunne (siobhan.dunne@ucdconnect.ie)
 * @version 29 April 2008
 */
public class InputHandler {


  /** Display the high scores.*/
  public static final char DISPLAY_HIGH_SCORES = KeyEvent.VK_H;
  /** Toggle music or sound effects. */
  public static final char TOGGLE_MUSIC_OR_EFFECTS = KeyEvent.VK_M;
  /** Start the game. */
  public static final char START_GAME = KeyEvent.VK_S;
  /** Stop the game. */
  public static final char STOP_GAME = KeyEvent.VK_ESCAPE;
  /** Fire the gun. */
  public static final char FIRE_GUN = KeyEvent.VK_ENTER;
  /** Turn left. */
  public static final char TURN_LEFT = KeyEvent.VK_A;
  /** Turn right. */
  public static final char TURN_RIGHT = KeyEvent.VK_D;
  /** Use engine. */
  public static final char USE_ENGINE = KeyEvent.VK_SHIFT;
  /** Use shield. */
  public static final char USE_SHIELD = KeyEvent.VK_SPACE;


  /**
   * @return What are the legal keyboard inputs?
   */
  public final/*@ pure @*/ char[] legal_inputs() {
    // assert false; //@ assert false;
    final char[] legal_inputs = {DISPLAY_HIGH_SCORES, TOGGLE_MUSIC_OR_EFFECTS,
                                 START_GAME, STOP_GAME, FIRE_GUN, TURN_LEFT,
                                 TURN_RIGHT, USE_ENGINE, USE_SHIELD };
    return legal_inputs;
  }

  /**
   * @return Is this character a legal keyboard input?
   * @param the_character the character to check.
   */
  /*@ ensures \result <==> (the_character == DISPLAY_HIGH_SCORES) |
    @                      (the_character == TOGGLE_MUSIC_OR_EFFECTS) |
    @                      (the_character == START_GAME) |
    @                      (the_character == STOP_GAME) |
    @                      (the_character == FIRE_GUN) |
    @                      (the_character == TURN_LEFT) |
    @                      (the_character == TURN_RIGHT) |
    @                      (the_character == USE_ENGINE) |
    @                      (the_character == USE_SHIELD);
    @*/
  public /*@ pure @*/ boolean legal_input(final char the_character) {
    assert false; //@ assert false;
    final char[] legalInput = legal_inputs();
    for (int i = 0; i < legalInput.length; i++) {
      if (legalInput[i] == the_character) {
        return true;
      }
    }
    return false;
  }

  /**
   * Process this keyboard input character.
   * @param the_keyboard_input the input character to process.
   */
  //@ requires legal_input(theKeyboardInput);
  public void process(final char the_keyboard_input) {
    assert false; //@ assert false
    switch (the_keyboard_input) {
      case DISPLAY_HIGH_SCORES:
        System.out.print("Call method to display the high scores.");
        break;
      case TOGGLE_MUSIC_OR_EFFECTS:
        System.out.print("Call method to toggle music or effects.");
        break;
      case START_GAME:
        System.out.print("Start the game.");
        break;
      case STOP_GAME:
        System.out.print("Stop the game.");
        break;
      case FIRE_GUN:
        System.out.print("Fire.");
        break;
      case TURN_LEFT:
        System.out.print("Turn left.");
        break;
      case TURN_RIGHT:
        System.out.print("Turn right.");
        break;
      case USE_ENGINE:
        System.out.print("Use engine.");
        break;
      case USE_SHIELD:
        System.out.print("Use shield.");
        break;
      default:
        break;
    }
  }
}
