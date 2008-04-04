package thrust.input;

/**
 * Processes and delegates each keyboard input received.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class InputHandler {
  /** Press h to Display the high score table. */
  public static final char DISPLAY_HIGH_SCORES = 'h';
  /** Press m to Toggle between hearing music or sound effects. */
  public static final char TOGGLE_MUSIC_OR_EFFECTS = 'm';
  /** Press n to Start a game. */
  public static final char START_GAME = 'n';
  /** Press q to stop a game. */
  public static final char STOP_GAME = 'q';
  /** Press . to Fire a bullet from the spaceship's gun. */
  public static final char FIRE_GUN = '.';
  /** Press a to Rotate the spaceship counterclockwise. */
  public static final char TURN_LEFT = 'a';
  /** Press s to Rotate the spaceship clockwise. */
  public static final char TURN_RIGHT = 's';
  /** Press , to Use the spaceship's engine to apply thrust forward. */
  public static final char USE_ENGINE = ',';
  /** Press space to Use the spaceships shield to protect itself or to gather fuel. */
  public static final char USE_SHIELD = ' ';

  /**
   * @return What are the legal keyboard inputs?
   */
  public /*@ pure @*/ char[] legal_inputs() {   
    char[] legal_inputs = new char[9];
    assert legal_inputs != null; //@ assert legal_inputs != null;
    legal_inputs[0] = DISPLAY_HIGH_SCORES;
    legal_inputs[1] = TOGGLE_MUSIC_OR_EFFECTS;
    legal_inputs[2] = START_GAME;
    legal_inputs[3] = STOP_GAME;
    legal_inputs[4] = FIRE_GUN;
    legal_inputs[5] = TURN_LEFT;
    legal_inputs[6] = TURN_RIGHT;
    legal_inputs[7] = USE_ENGINE;
    legal_inputs[8] = USE_SHIELD;
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
  public /*@ pure @*/ boolean legal_input(char the_character) {   
    char[] legal_inputs = legal_inputs();
    assert legal_inputs != null; //@ assert legal_inputs != null;
    for(int i = 0; i < legal_inputs.length; i++)
    {
      if(legal_inputs[i] == the_character)
      {
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
  public void process(char the_keyboard_input) {
    assert false; //@ assert false;
  }
}
