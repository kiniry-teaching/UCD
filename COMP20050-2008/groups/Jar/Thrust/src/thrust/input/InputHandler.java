package thrust.input;

/**
 * Processes and delegates each keyboard input received.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class InputHandler {
  /** An unknown character code. */
  /**private static final char UNKNOWN_CHAR = '\0';
  /** Character h to display high scores. */
  public static final char DISPLAY_HIGH_SCORES = 'h';
  /** Character m switch between music and SFX. */
  public static final char TOGGLE_MUSIC_OR_EFFECTS = 'm';
  /** Character [space] to start game. */
  public static final char START_GAME = '\u00A0';
  /** Character [escape] to stop game. */
  public static final char STOP_GAME = '\u001B';
  /** Character [enter] to fire gun. */
  public static final char FIRE_GUN = '\n';
  /** Character a to turn left. */
  public static final char TURN_LEFT = 'a';
  /** Character s to turn right. */
  public static final char TURN_RIGHT = 's';
  /** Character [shift] to thrust. */
  public static final char USE_ENGINE = '\u000F';
  /** Character [space] to turn on shield/pickup. */
  public static final char USE_SHIELD = '\u00A0';

  /**
   * @return What are the legal keyboard inputs?
   */
  public final /*@ pure @*/ char[] legalInputs() {
    final char[] inputs = {DISPLAY_HIGH_SCORES, TOGGLE_MUSIC_OR_EFFECTS,
                             START_GAME, STOP_GAME, FIRE_GUN, TURN_LEFT,
                               TURN_RIGHT, USE_ENGINE, USE_SHIELD};
    //@ assert true;
    return inputs;
  }

  
  /*@ ensures \result <==> (theCharacter == DISPLAY_HIGH_SCORES) |
    @                      (theCharacter == TOGGLE_MUSIC_OR_EFFECTS) |
    @                      (theCharacter == START_GAME) |
    @                      (theCharacter == STOP_GAME) |
    @                      (theCharacter == FIRE_GUN) |
    @                      (theCharacter == TURN_LEFT) |
    @                      (theCharacter == TURN_RIGHT) |
    @                      (theCharacter == USE_ENGINE) |
    @                      (theCharacter == USE_SHIELD);
    @*/
  /**
   * @return Is this character a legal keyboard input?
   * @param theCharacter the character to check.
   */
  public final /*@ pure @*/ boolean legalInput(final char theCharacter) {
    char[] inputs = legalInputs();
    for (int i = 0; i < inputs.length - 1; i++) {
      if (theCharacter == inputs[i]) {
        return true;
      }
    }
    return false;
  }

  /**
   * Process this keyboard input character.
   * @param theKeyboardInput the input character to process.
   */
  //@ requires legalInput(theKeyboardInput);
  public void process(final char theKeyboardInput) {
    //@ assert false;
  }
}
