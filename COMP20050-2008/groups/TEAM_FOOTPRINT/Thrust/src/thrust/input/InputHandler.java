
//class written by Daire O'Doherty 06535691 3/4/08
//Just trying to set up what the legal inputs for the game are, and how the computer checks if what is pressed is legal

package thrust.input;

public class InputHandler {
 
  private static final char UNKNOWN_CHAR = '\0';
    public static final char 
      DISPLAY_HIGH_SCORES = 'h', //when h is pressed, the high scores will be displayed
      TOGGLE_MUSIC_OR_SOUND_EFFECTS = 'm', // when m is pressed the music will be toggled
      START_GAME = '\u0020', // when the space key is pressed the game will start
      STOP_GAME = '\u001B', //when escape is pressed the game will stop
      FIRE_GUN = '\r',  //when return is pressed the ship will fire
      TURN_LEFT = 'a',  // when a is pressed the ship will turn right
      TURN_RIGHT = 's', // when s is pressed the ship will turn right
      USE_ENGINE = 'g', //  when g is pressed the ship will use its engine
      USE_SHIELD = 'd'; //  when d is pressed the shield will be used
    //couldn't find ascii or unicode for shift
    
  /**
   * @return What are the legal keyboard inputs?
   */
  public /*@ pure @*/ char[] legal_inputs() {
     //@ assert false;
    
    char[] legal_inputs = new char[9];
    legal_inputs[0]=DISPLAY_HIGH_SCORES;
    legal_inputs[1] = TOGGLE_MUSIC_OR_SOUND_EFFECTS;
    legal_inputs[2] =  START_GAME;
    legal_inputs[3] = STOP_GAME;
    legal_inputs[4]= FIRE_GUN;
    legal_inputs[5]=TURN_LEFT ;
    legal_inputs[6] = TURN_RIGHT;
    legal_inputs[7]=USE_ENGINE;
    legal_inputs[8]= USE_SHIELD;
  
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
    @                     (k == USE_SHIELD);
    @*/
  //@requires true
  public /*@ pure @*/ boolean legal_input(char k) {
     //@ assert false;
    
    //loop through the legal_inputs array
    for(int i = 0; i <= legal_inputs().length; i++)
      {
                                if (legal_inputs()[i] == k){
                                        return true; //if the character typed is the same as one of the characters in the input
                                }
      }
    return false;
  }

  /**
   * Process keyboard input character 'k'.
   */
  //@ requires legal_input(k);
  public void process(char k) {
     //@ assert false;
   if(legal_input(k) == true){
    if(k == DISPLAY_HIGH_SCORES){
      //display high scores
    }
    else if (k == TOGGLE_MUSIC_OR_SOUND_EFFECTS){
      //toggle music or sound effects
      
    }
    else if(k == START_GAME){
      
      //start the game
    }
    
    else if(k == STOP_GAME){     
      //stop the game
    }
    else if(k == FIRE_GUN){
      //Fire the gun
    }
    else if(k == TURN_LEFT ){
      //turn ship left
         }
    else if(k==TURN_RIGHT){
      //turn ship right
     
      
    }
    else if(k==USE_ENGINE){
     
    }
    else if(k == USE_SHIELD){
      //use the shield
     
      
    }
   }
   else{
     //this is not a legal input
      }
}
}
  