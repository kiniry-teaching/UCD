package thrust.input;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;



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
  public static final char START_GAME = (char) 13;
  /** Started by Enter. */
  public static final char STOP_GAME = (char) 27;
  /** Halts game using Esc key. */
  public static final char FIRE_GUN = (char) 32;
  /** Spacebar. */
  public static final char TURN_LEFT = 'a';
  /** hit a to turn left. */
  public static final char TURN_RIGHT = 'd';
  /** hit d to turn right. */
  public static final char USE_ENGINE = 'w';
  /** hit w to thrust. */
  public static final char USE_SHIELD = 'k';
  /** hit i to use shield. */
  /**
   * @return What are the legal keyboard inputs?
   */
  public static char legal_inputs[]=new char [9]; {
    //assert false; //@ assert false;
    //return null;
	legal_inputs[0] = DISPLAY_HIGH_SCORES;
	legal_inputs[1] = TOGGLE_MUSIC_OR_EFFECTS;
	legal_inputs[2] = START_GAME;
	legal_inputs[3] = STOP_GAME;
	legal_inputs[4] = FIRE_GUN;
	legal_inputs[5] = TURN_LEFT;
	legal_inputs[6] = TURN_RIGHT;
	legal_inputs[7] = USE_ENGINE;
	legal_inputs[8] = USE_SHIELD;
	
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
 public char keyCode;
  public char keyPressed(KeyEvent e){
     keyCode = (char) e.getKeyCode();
     return keyCode;
  }
  
  public /*@ pure @*/ boolean legal_input(){
      
    
    for(int i=0; i<9; i++){
        if (legal_inputs[i] == keyCode){
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
