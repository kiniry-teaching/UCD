package thrust.input;

public class InputHandler {
  public static final char DISPLAY_HIGH_SCORES = 'h';
  public static final char TOGGLE_MUSIC_OR_SOUND_EFFECTS = 'm';
  public static final char START_GAME = '\u00A0'; //space
  public static final char STOP_GAME = '\u001B'; //escape
  public static final char FIRE_GUN = 'f';
  public static final char TURN_LEFT = 'a';
  public static final char TURN_RIGHT = 'd';
  public static final char USE_ENGINE = 'w';
  public static final char USE_SHIELD = 's';

  /**
   * @return What are the legal keyboard inputs?
   */
  public /*@ pure @*/ char[] legal_inputs() {
    final char[] legal = {DISPLAY_HIGH_SCORES, TOGGLE_MUSIC_OR_SOUND_EFFECTS, START_GAME, STOP_GAME, FIRE_GUN, TURN_LEFT, TURN_RIGHT, USE_ENGINE, USE_SHIELD};
    return legal;
  }

  /**
   * Is character 'k' a legal keyboard input?
   */
  /*@ ensures \result <==> (k == DISPLAY_HIGH_SCORES) |
    @                      (k == TOGGLE_MUSIC_OR_SOUND_EFFECTS) |
    @                      (k == START_GAME) |
    @                      (k == STOP_GAME) |
    @                      (k == FIRE_GUN) |
    @                      (k == TURN_LEFT) |
    @                      (k == TURN_RIGHT) |
    @                      (k == USE_ENGINE) |
    @                      (k == USE_SHIELD);
    @*/
  public /*@ pure @*/ boolean legal_input(char k) {
      boolean legal=false;
      char[] characters = new char[9];
    	characters =  legal_inputs();
    	for (int i=0; i<characters.length; i++) {
    		if (k == characters[i]) {
    			legal = true;
    		}
    	}
    
    	return legal;
  }

  /**
   * Process keyboard input character 'k'.
   */
  //@ requires legal_input(k);
  void process(char k) {
      if(legal_input(k) == false) {
          System.out.println("ERROR!!! ILLEGAL CHARACTER!!!");
    } else
      //Process the character, k	
      assert false; //@ assert false;
  }
}
