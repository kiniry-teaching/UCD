


//revised Naomi O' Reilly 04-04-2008

package thrust.input;

public class InputHandler {
  private static final char UNKNOWN_CHAR = '\0';
  public static final char DISPLAY_HIGH_SCORES ='h',
    TOGGLE_MUSIC_OR_SOUND_EFFECTS = 'm',
    START_GAME = ' ',
    STOP_GAME = 27,
    FIRE_GUN = 'r',
    TURN_LEFT = 'a',
    TURN_RIGHT ='s',
    USE_ENGINE = 16,
    USE_SHIELD =' ';
   private  boolean gameStarted;

  /**
   * @return What are the legal keyboard inputs?
   */
  public /*@ pure @*/ char[] legal_inputs() {
   
    char[] legal_inputs = {DISPLAY_HIGH_SCORES,TOGGLE_MUSIC_OR_SOUND_EFFECTS,START_GAME,STOP_GAME,FIRE_GUN,TURN_LEFT,TURN_RIGHT,USE_ENGINE,USE_SHIELD};
		  
		    return legal_inputs;
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
   
  
       
    return k == DISPLAY_HIGH_SCORES || k == TOGGLE_MUSIC_OR_SOUND_EFFECTS || k == START_GAME || k == STOP_GAME || k == FIRE_GUN || k == TURN_LEFT || k == TURN_RIGHT || k == USE_ENGINE || k == USE_SHIELD;
   
  }

  /**
   * Process keyboard input character 'k'.
   */
  //@ requires legal_input(k);
  void process(char k) {
  
    switch(k){
    case DISPLAY_HIGH_SCORES:/**what will happen if h is pressed**/ break;
    case TOGGLE_MUSIC_OR_SOUND_EFFECTS:/**what will happen if m is pressed**/ break;
    case STOP_GAME:/**what will happen if space is pressed**/gameStarted = false; break;
    case FIRE_GUN:/**what will happen if r is pressed**/ break;
    case TURN_LEFT:/**what will happen if a is pressed**/ break;
    case TURN_RIGHT:/**what will happen if s is pressed**/ break;
    case ' ':/**what will happen if ' ' is pressed**/if(gameStarted){/**use shield**/}else{ /**Start game**/ gameStarted = true;}  break;
      }
 
 }
}
