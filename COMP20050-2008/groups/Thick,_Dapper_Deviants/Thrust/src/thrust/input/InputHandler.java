package thrust.input;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;



/**sfsa
 * Processes and delegates each keyboard input received.
 * @author stephen
 * @version 30 April 2008
 */
public class InputHandler implements KeyListener {
  /** An unknown character code. */
  //private static final char UNKNOWN_CHAR = '\0';
  /** Fill in this comment. */
  //public boolean my_keyDown (final Event a_e, final int an_key) {
  //  
  //}
  
  
  
  
  /** Calls high score screen. */
  public static final char DISPLAY_HIGH_SCORES = 'h';
  /** Sets music and effects to false or true. */
  public static final char TOGGLE_MUSIC_OR_EFFECTS = 'm';
  /** Started by Enter. */
  public static final char START_GAME = (char) 13;
  /** Halts game using Esc key. */
  public static final char STOP_GAME = (char) 27;
  /** Spacebar. */
  public static final char FIRE_GUN = (char) 32;
  /** hit a to turn left. */
  public static final char TURN_LEFT = 'a';
  /** hit d to turn right. */
  public static final char TURN_RIGHT = 'd';
  /** hit w to thrust. */
  public static final char USE_ENGINE = 'w';
  /** hit i to use shield. */
  public static final char USE_SHIELD = 'k';
  
  /**
   * @return What are the legal keyboard inputs?
   */
  public char[] legal_inputs() {
    //assert false; //@ assert false;
    //return null;
  final char legal_inputs[] = new char[9];
  legal_inputs[0] = DISPLAY_HIGH_SCORES;
  legal_inputs[1] = TOGGLE_MUSIC_OR_EFFECTS;
  legal_inputs[2] = START_GAME;
  legal_inputs[3] = STOP_GAME;
  legal_inputs[4] = FIRE_GUN;
  legal_inputs[5] = TURN_LEFT;
  legal_inputs[6] = TURN_RIGHT;
  legal_inputs[7] = USE_ENGINE;
  legal_inputs[8] = USE_SHIELD;
  assert legal_inputs != null;
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
 //final char keyCode;
  
  
 
  public /*@ pure @*/ boolean legal_input(final char the_character) {
    final char[] legal_inputs = legal_inputs();
    assert (legal_inputs != null);
    
    for(int i=0; i<legal_inputs.length; i++){
        if (legal_inputs[i] == the_character){
          return true;
        }
      }
    return false;
  } 
  addKeyListener(new KeyListener)
  
  public void keyPressed(KeyEvent e){
    final char keyCode = (char) e.getKeyCode();
    
 }

  /**
   * Process this keyboard input character.
   * @param the_keyboard_input the input character to process.
   */
  //@ requires legal_input(the_keyboard_input);
  public void process(char the_keyboard_input) {
    //assert false; //@ assert false;
    /** Calls high score screen. */
    if(the_keyboard_input == DISPLAY_HIGH_SCORES){
      assert true;
    }
    /** Sets music and effects to false or true. */
    else if (the_keyboard_input == TOGGLE_MUSIC_OR_EFFECTS){
      assert true;
    }
    /** Starts the game. */
    else if (the_keyboard_input == START_GAME){
      assert true;
    }
    /** Ends the game. */
    else if (the_keyboard_input == STOP_GAME){
      
    }
    /** Fires the gun. */
    else if(the_keyboard_input == FIRE_GUN){
      assert true;
    }
    /** Turn spaceship left. */
    else if(the_keyboard_input == TURN_LEFT){
      assert true;
    }
    /** Turn spaceship right. */
    else if(the_keyboard_input == TURN_RIGHT){
      assert true;
    }
    /** Engages engine. */
    else if(the_keyboard_input == USE_ENGINE){
      assert true;
    }
    /** Invokes shield. */
  else if(the_keyboard_input == USE_SHIELD){
    assert true;
  }
    /** Not a valid command. */
  else{
    assert false;
  }
  }
  
  public void keyReleased(KeyEvent e) {
    // TODO Auto-generated method stub
    
  }

  public void keyTyped(KeyEvent e) {
    // TODO Auto-generated method stub
    
  }
  /*public static void main(String[] args){
    typingArea = new JTextField(20);
    typingArea.addKeyListener(this);
    while (h.keyPressed(e) != STOP_GAME){
      System.out.println((char) e.getKeyCode());
      //return null;
    }*/
    
    
  }

  
}

