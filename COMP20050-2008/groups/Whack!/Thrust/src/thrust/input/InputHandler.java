package thrust.input;

/**
 * Processes and delegates each keyboard input received.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class InputHandler {
  /** An unknown character code. */
  private static final char UNKNOWN_CHAR = '\0';
  /** Fill in this comment. */
  public static final char DISPLAY_HIGH_SCORES = 'd';
  /** Fill in this comment. */
  public static final char TOGGLE_MUSIC_OR_EFFECTS = 'm';
  /** Fill in this comment. */
  public static final char START_GAME = 's';
  /** Fill in this comment. */
  public static final char STOP_GAME = 'q';
  /** Fill in this comment. */
  public static final char FIRE_GUN = 'f';
  /** Fill in this comment. */
  public static final char TURN_LEFT = 37;
  /** Fill in this comment. */
  public static final char TURN_RIGHT = 39;
  public static final char USE_ENGINE = 32;
  /** Fill in this comment. */
  public static final char USE_SHIELD = 38;

  /**
   * @return What are the legal keyboard inputs?
   */
  public /*@ pure @*/ char[] legal_inputs() {
    final char[] inputs = {DISPLAY_HIGH_SCORES, TOGGLE_MUSIC_OR_EFFECTS, START_GAME, STOP_GAME, FIRE_GUN,
                           TURN_LEFT, TURN_RIGHT, USE_ENGINE, USE_SHIELD};

    return inputs;
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
    boolean quit = false;
    char[] inputs = legal_inputs();
    for(int i = 0; i < inputs.length; i++){
      if(the_character == inputs[i]){
        quit = true;
      }
    }
    return quit;
  }

  /**
   * Process this keyboard input character.
   * @param the_keyboard_input the input character to process.
   */
  //@ requires legal_input(the_keyboard_input);
  public void process(char the_keyboard_input) {

    if(the_keyboard_input == 'd'){
      System.out.println("Should call the DISPLAY_HIGH_SCORES method");
    }
    if(the_keyboard_input == 'm'){
      System.out.println("Should call the TOGGLE_MUSIC_OR_EFFECTS method");
    }
    if(the_keyboard_input == 's'){
      System.out.println("Should call the START_GAME method");
    }
    if(the_keyboard_input == 'q'){
      System.out.println("Should call the STOP_GAME method");
    }
    if(the_keyboard_input == 'f'){
      System.out.println("Should call the FIRE_GUN method");
    }
    if(the_keyboard_input == 37){
      System.out.println("Should call the TURN_LEFT method");
    }
    if(the_keyboard_input == 39){
      System.out.println("Should call the TURN_RIGHT method");
    }
    if(the_keyboard_input == 32){
      System.out.println("Should call the USE_ENGINE method");
    }
    if(the_keyboard_input == 38){
      System.out.println("Should call the USE_SHIELD method");
    }
    assert false; //@ assert false;
  }
}
