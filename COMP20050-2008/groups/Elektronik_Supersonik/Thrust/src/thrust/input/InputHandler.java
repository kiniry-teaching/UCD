package thrust.input;
import java.awt.event.KeyEvent;

/**
 * Processes and delegates each keyboard input received.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class InputHandler {
  /** An unknown character code. */
  private static final char UNKNOWN_CHAR = '\0';
  /** Character code for displaying high scores (F12) */
  public static final char DISPLAY_HIGH_SCORES = KeyEvent.VK_F12;
  /** Character code for toggling sound and music (S) */
  public static final char TOGGLE_MUSIC_OR_EFFECTS = KeyEvent.VK_S;
  /** Character code to start the game (Enter) */
  public static final char START_GAME = KeyEvent.VK_ENTER;
  /** Character code to stop (pause) the game (Pause) */
  public static final char STOP_GAME = KeyEvent.VK_PAUSE;
  /** Character code to fire the gun (Space) */
  public static final char FIRE_GUN = KeyEvent.VK_SPACE;
  /** Character code to turn left (Left arrow) */
  public static final char TURN_LEFT = KeyEvent.VK_LEFT;
  /** Character code to turn right (Right arrow) */
  public static final char TURN_RIGHT = KeyEvent.VK_RIGHT;
  /** Character code to use engine (thrust) (Up arrow) */
  public static final char USE_ENGINE = KeyEvent.VK_UP;
  /** Character code to enable shield (Shift) */
  public static final char USE_SHIELD = KeyEvent.VK_SHIFT;

  /**
   * @return What are the legal keyboard inputs?
   */
  public /*@ pure @*/ char[] legal_inputs() {
    char legal[] = new char[9];
    legal[0] = KeyEvent.VK_F12;
    legal[1] = KeyEvent.VK_S;
    legal[2] = KeyEvent.VK_ENTER;
    legal[3] = KeyEvent.VK_PAUSE;
    legal[4] = KeyEvent.VK_SPACE;
    legal[5] = KeyEvent.VK_UP;
    legal[6] = KeyEvent.VK_SHIFT;
    legal[7] = KeyEvent.VK_LEFT;
    legal[8] = KeyEvent.VK_RIGHT;
    return legal;
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
  public /*@ pure @*/ boolean legal_input(char the_character) {
    boolean retBool = false;
    for(int i = 0; i < legal_inputs().length; ++i) {
      if(legal_inputs()[i] == the_character) {
        retBool = true;
      }
    }
    return retBool;
  }

  /**
   * Process this keyboard input character.
   * @param the_keyboard_input the input character to process.
   */
  //@ requires legal_input(the_keyboard_input);
  public void process(char the_keyboard_input) {
    assert false; //@ assert false;
  }
}
