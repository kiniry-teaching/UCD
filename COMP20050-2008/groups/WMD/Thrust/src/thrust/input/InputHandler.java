package thrust.input;

/**
 * Processes and delegates each keyboard input received.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class InputHandler {
  /** An unknown character code. */
  private static final char UNKNOWN_CHAR = '\0';
  /** Display high scores */
  public static final char DISPLAY_HIGH_SCORES = 'h';
  /** Toggle music or sound effects */
  public static final char TOGGLE_MUSIC_OR_EFFECTS = 'm';
  /** Start the game */
  public static final char START_GAME = "space";
  /** Stop the game */
  public static final char STOP_GAME = "escape";
  /** Fire Gun */
  public static final char FIRE_GUN = "return";
  /** Turn left */
  public static final char TURN_LEFT = 'a';
  /** Turn right */
  public static final char TURN_RIGHT = 's';
  /** Use engine */
  public static final char USE_ENGINE = "shift";
  /** Use shield */
  public static final char USE_SHIELD = "space";

  /**
   * @return What are the legal keyboard inputs?
   */
  public /*@ pure @*/ char[] legal_inputs() {
    assert false; //@ assert false;
    char[] input = new char[9];
    input[0] = DISPLAY_HIGH_SCORES;
    input[1] = TOGGLE_MUSIC_OR_EFFECTS;
    input[2] = START_GAME;
    input[3] = STOP_GAME;
    input[4] = FIRE_GUN;
    input[5] = TURN_LEFT;
    input[6] = TURN_RIGHT;
    input[7] = USE_ENGINE;
    input[8] = USE_SHIELD;
    return input;
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
   
    char[] legal_input = legal_inputs();
    for(int i=0; i<legal_input.length; i++){
      if(legal_input[i] == the_character){
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
    assert false; //@ assert false
    char[] inputs = legal_inputs();
    if(legal_input(the_keyboard_input)){
      for(int i=0; i<inputs.length; i++){
        if(inputs[i] == the_keyboard_input){
          //call method depending on the keyboard input
        }
      }
    }
  }
}
