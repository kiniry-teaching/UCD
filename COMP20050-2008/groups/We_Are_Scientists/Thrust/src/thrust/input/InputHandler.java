package thrust.input;


import java.awt.event.KeyEvent;
/**
 * Processes and delegates each keyboard input received.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 *
 */
public class InputHandler {
  /** An unknown character code. */
 // private static final char UNKNOWN_CHAR = '\0';
  /**  command to display the high scores: h. */
  public static final char DISPLAY_HIGH_SCORES = KeyEvent.VK_H;
  /** command to toggle the music or effects: m. */
  public static final char TOGGLE_MUSIC_OR_EFFECTS = KeyEvent.VK_M;
  /** begins the game on level one: enter. */
  public static final char START_GAME = KeyEvent.VK_ENTER;
  /** quits the game: escape. */
  public static final char STOP_GAME = KeyEvent.VK_ESCAPE;
  /** fires the ships gun 4 bullets: space. */
  public static final char FIRE_GUN = KeyEvent.VK_SPACE;;
  /** turns the ship anti_clockwise: left arrow. */
  public static final char TURN_LEFT = KeyEvent.VK_LEFT;
  /** turns the ship clockwise: right arrow. */
  public static final char TURN_RIGHT = KeyEvent.VK_RIGHT;
  /** thrust uses fuel: up arrow.*/
  public static final char USE_ENGINE = KeyEvent.VK_UP;
  /** use the shield and tractor beam, uses fuel: s.*/
  public static final char USE_SHIELD = KeyEvent.VK_S;

  /**
   * @return What are the legal keyboard inputs?
   */
  public final /*@ pure @*/  char[] legal_inputs() {
    final char[] legal_inputs = {DISPLAY_HIGH_SCORES,
      TOGGLE_MUSIC_OR_EFFECTS, START_GAME,
      STOP_GAME, FIRE_GUN, TURN_LEFT, TURN_RIGHT, USE_ENGINE,
      USE_SHIELD };
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
  /**
   * @return Is this character a legal keyboard input?
   * @stuff
   */
  public final /*@ pure @*/ boolean legalInput(final char the_character) {
    boolean legal = false;
    for (int i = 0; i < legal_inputs().length; i++)
    {
      if (legal_inputs()[i] == the_character) {
        legal = true;
      }
    }
    return legal;
  }

    /**switch (the_character)
    {
      case DISPLAY_HIGH_SCORES:
        System.out.print("display the scores");
        break;
      case TOGGLE_MUSIC_OR_EFFECTS:
        System.out.print("turn music on or off");
        break;
      case START_GAME:
        System.out.print("begin the game");
        break;
      case STOP_GAME:
        System.out.print("end and quit the game");
        break;
      case FIRE_GUN:
        System.out.print("fires the gun of the ship 4 bullets max");
        break;
      case TURN_LEFT:
        System.out.print("turn left");
        break;
      case TURN_RIGHT:
        System.out.print("display the scores");
        break;
      case USE_ENGINE:
        System.out.print("display the scores");
        break;
      case USE_SHIELD:
        System.out.print("display the scores");
        break;
      default:
        break;
    }
    return true;*/


  /**
   * Process this keyboard input character.
   * @param the_keyboard_input the input character to process.
   */
  //@ requires legal_input(the_keyboard_input);
  public void process(final char the_keyboard_input) {
    //assert false; //@ assert false;
  }
}
