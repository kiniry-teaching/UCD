package thrust.input;

/**
 * Processes and delegates each keyboard input received.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class InputHandler 
{
    /** An unknown character code. */
    private static final char UNKNOWN_CHAR = '\0';
    /** Fill in this comment. */
    //public static final char DISPLAY_HIGH_SCORES = UNKNOWN_CHAR;
    public static final int DISPLAY_HIGH_SCORES = 104;
    /** Fill in this comment. */
    // public static final char TOGGLE_MUSIC_OR_EFFECTS = UNKNOWN_CHAR;
    public static final int TOGGLE_MUSIC_OR_EFFECTS = 109;
    /** Fill in this comment. */
    // public static final char START_GAME = UNKNOWN_CHAR;
    public static final int START_GAME = 32;
    /** Fill in this comment. */
    // public static final char STOP_GAME = UNKNOWN_CHAR;
    public static final int STOP_GAME = 27;
    /** Fill in this comment. */
    // public static final char FIRE_GUN = UNKNOWN_CHAR;
    public static final int FIRE_GUN = 13;
    /** Fill in this comment. */
    // public static final char TURN_LEFT = UNKNOWN_CHAR;
    public static final int TURN_LEFT = 97;
    /** Fill in this comment. */
    //public static final char TURN_RIGHT = UNKNOWN_CHAR;
    public static final int TURN_RIGHT = 115;
     /** Fill in this comment. */
    //public static final char USE_ENGINE = UNKNOWN_CHAR;
    public static final int USE_ENGINE = 15;
    /** Fill in this comment. */
    // public static final char USE_SHIELD = UNKNOWN_CHAR;
    public static final int USE_SHIELD = 32;
    
  /**
   * @return What are the legal keyboard inputs?
   */
    public /*@ pure @*/ char[] legal_inputs()
    {
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
    public /*@ pure @*/ boolean legal_input(char the_character)
    {
    assert false; //@ assert false;
    return false;
    }

  /**
   * Process this keyboard input character.
   * @param the_keyboard_input the input character to process.
   */
  //@ requires legal_input(the_keyboard_input);
    public void process(char the_keyboard_input)
    {
    assert false; //@ assert false;
    }
}
