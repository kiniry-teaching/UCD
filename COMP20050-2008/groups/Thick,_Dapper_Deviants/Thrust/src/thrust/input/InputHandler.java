package thrust.input;


/**sfsa
 * Processes and delegates each keyboard input received.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class InputHandler {
  /** An unknown character code. */
  //private static final char UNKNOWN_CHAR = '\0';
  /** Fill in this comment. */
	//public boolean my_keyDown (final Event a_e, final int an_key) {
	//	
	//}
  public static final char DISPLAY_HIGH_SCORES = 'h';
  /** Calls high score screen. */
  public static final char TOGGLE_MUSIC_OR_EFFECTS = 'm';
  /** Sets music playing and effects to false. */
  public static final char START_GAME = 13;
  /** Started by Enter (Ascii code equivilant). */
  public static final char STOP_GAME = 'escape';
  /** Halts game using Esc key. */
  public static final char FIRE_GUN = 32;
  /** Spacebar. */
  public static final char TURN_LEFT = 'a';
  /** hit a to turn left. */
  public static final char TURN_RIGHT = 'd';
  /** hit d to turn right. */
  public static final char USE_ENGINE = 'w';
  /** hit w to thrust. */
  public static final char USE_SHIELD = 'i';
  /** hit i to use shield. */
  /**
   * @return What are the legal keyboard inputs?
   */
  public /*@ pure @*/ char[] legal_inputs() {
    assert false; //@ assert false;
    return null;
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
    assert false; //@ assert false;
    return false;
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
