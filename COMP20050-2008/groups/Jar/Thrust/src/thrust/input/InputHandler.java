package thrust.input;

/**
 * Processes and delegates each keyboard input received.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class InputHandler {
  /** An unknown character code. */
  private static final char UNKNOWN_CHAR = '\0';
  /** Character to display high scores. */
  public static final char DISPLAY_HIGH_SCORES = UNKNOWN_CHAR;
  /** Character to switch between music and SFX. */
  public static final char TOGGLE_MUSIC_OR_EFFECTS = UNKNOWN_CHAR;
  /** Character to start game. */
  public static final char START_GAME = UNKNOWN_CHAR;
  /** Character to stop game. */
  public static final char STOP_GAME = UNKNOWN_CHAR;
  /** Character to fire gun. */
  public static final char FIRE_GUN = UNKNOWN_CHAR;
  /** Character to turn left. */
  public static final char TURN_LEFT = UNKNOWN_CHAR;
  /** Character to turn right. */
  public static final char TURN_RIGHT = UNKNOWN_CHAR;
  /** Character to thrust. */
  public static final char USE_ENGINE = UNKNOWN_CHAR;
  /** Character to turn on shield/pickup. */
  public static final char USE_SHIELD = UNKNOWN_CHAR;

  /**
   * @return What are the legal keyboard inputs?
   */
  public final /*@ pure @*/ char[] legal_inputs() {
    final char[] inputs = {DISPLAY_HIGH_SCORES, TOGGLE_MUSIC_OR_EFFECTS,
                             START_GAME, STOP_GAME, FIRE_GUN, TURN_LEFT,
                               TURN_RIGHT, USE_ENGINE, USE_SHIELD};
    assert false; //@ assert false;
    return inputs;
  }

  /**
   * @return Is this character a legal keyboard input?
   * @param the_character the character to check.
   * @param inputs array containing legal inputs
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
    char[] inputs = legal_inputs();
    for (int i = 0; i < inputs.length - 1; i++) {
      if (the_character == inputs[i]) {
        return true;
      }
    }
    return false;
  }

  /**
   * Process this keyboard input character.
   * @param the_keyboard_input the input character to process.
   */
  //@ requires legal_input(the_keyboard_input);
  public void process(final char the_keyboard_input) {
    assert false; //@ assert false;
  }
}
