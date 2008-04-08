package thrust.input;


//import java.awt.event.KeyEvent;
/**
 * Processes and delegates each keyboard input received.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 * holly ursula simon - worked on input physics and audio equally
 */
public class InputHandler {
  /** An unknown character code. */
 // private static final char UNKNOWN_CHAR = '\0';
  /** this is the command to display the high scores. */
  public static final char DISPLAY_HIGH_SCORES = 'h';
  /** command to turn the music effects on or off.*/
  public static final char TOGGLE_MUSIC_OR_EFFECTS = 'm';
  /** begins the game on level one. */
  public static final char START_GAME = '\u00A0';
  /** quits the game. */
  public static final char STOP_GAME = '\u001B';
  /** fires the ships gun 4 bullets. */
  public static final char FIRE_GUN = '\n';
  /** the key a turns the ship anti anti_clockwise. */
  public static final char TURN_LEFT = 'a';
  /** turns the ship clockwise. */
  public static final char TURN_RIGHT = 's';
  /** thrust uses fuel.*/
  public static final char USE_ENGINE = '\u000F';
  /** use the shield and tractor beam. Uses fuel.*/
  public static final char USE_SHIELD = '\u00A1';

  /**
   * @return What are the legal keyboard inputs?
   */
  public final /*@ pure @*/  char[] legal_inputs() {
    final char[] legal_inputs = {DISPLAY_HIGH_SCORES,
      TOGGLE_MUSIC_OR_EFFECTS, START_GAME,
      STOP_GAME, FIRE_GUN, TURN_LEFT, TURN_RIGHT, USE_ENGINE,
      USE_SHIELD };
    //assert false; //@ assert false;
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

    switch (the_character)
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
    return true;
   /* if ((the_character == 'h') ||
        (the_character == 'm')  ||
        (the_character == '\u00A0') ||
        (the_character == '\u001B') || (the_character == '\n') ||
        (the_character == 'a') ||
        (the_character == 's') || (the_character == '\u000F')) {

      return true;
    }
    //assert false; //@ assert false;
    return false;
    */
  }

  /**
   * Process this keyboard input character.
   * @param the_keyboard_input the input character to process.
   */
  //@ requires legal_input(the_keyboard_input);
  public void process(final char the_keyboard_input) {
    //assert false; //@ assert false;
  }
}
