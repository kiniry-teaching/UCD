
//class written by Daire O'Doherty 06535691 3/4/08

//Just trying to set up what the legal inputs for the game are, and how the computer checks if what is pressed is legal

//Daire O'Doherty 06535691 reworked on it 5/4/08, havn't been able to get in touch with one of my team members in a few weeks, other member Sinead morley
//said that she would implement the audio, I have started a bit of the Physics myself, as i don't know if Lane is going to do it
package thrust.input;

public class InputHandler {
  
 

    
  public static final char DISPLAY_SCORES = 'h'; 
//when h is pressed, the high scores will be displayed
  public static final char TOGGLE_MUSIC = 'm'; 
//when m is pressed the music will be toggled
  public static final char START_GAME = '32'; 
//space key is pressed the game will start
  public static final char STOP_GAME = '27'; //when escape is pressed the game will stop
  public static final char FIRE_GUN = '\r'; //when return is pressed the ship will fire
  public static final char     TURN_LEFT = 'a';  // when a is pressed the ship will turn right
  public static final char     TURN_RIGHT = 's'; // when s is pressed the ship will turn right
  public static final char     USE_ENGINE = '15'; //  when [shift] is pressed the ship will use its engine
  public static final char     USE_SHIELD = 'd'; //  when d is pressed the shield will be used
  
    //researched ASCII code online and found 32,27,15 the ones im looking for
  /**
   * @return What are the legal keyboard inputs?
   */
  public /*@ pure @*/ char[] legal_inputs() {
     //@ assert false;
    
    char[] legal_inputs={DISPLAY_SCORES,TOGGLE_MUSIC,
                           START_GAME,STOP_GAME,FIRE_GUN,TURN_LEFT,
                           TURN_RIGHT ,USE_ENGINE, USE_SHIELD};
  
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
     
    
    //loop through the legal_inputs array
    for(int i = 0; i <= legal_inputs().length; i++)
      {
                                if (legal_inputs()[i] == k){
                                        return true; //if the character typed is the same as one of the characters in the input
                                }
      }
    return false;//otherwise return false
  }

  /**
   * Process keyboard input character 'k'.
   */
  //@ requires legal_input(k);
  public void process(char k) {
     //@ assert false;
   if(legal_input(k) == true){
    if(k == DISPLAY_SCORES){
      //display high scores
    }
    else if (k == TOGGLE_MUSIC){
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
  