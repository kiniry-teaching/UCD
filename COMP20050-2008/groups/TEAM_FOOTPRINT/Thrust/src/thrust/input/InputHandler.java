
/**class written by Daire O'Doherty 06535691 3/4/08

Just trying to set up what the legal inputs for the game are, and how the computer checks if what is pressed is legal

Daire O'Doherty 06535691 reworked on it 5/4/08, havn't been able to get in touch with one of my team members in a few weeks, other member Sinead morley
said that she would implement the audio, I have started a bit of the Physics myself, as i don't know if Lane is going to do it
Revised again on 8/4/08 with a little help from Fintan, still can't get rid of some of the errors, told to ignore them,
told to use System.out.print, this pulled up more errors, told to ignore them
*/
package thrust.input;
import java.util.logging.Logger;
/**
 *
 * @author "Daire o Doherty 06535691 (daireod@gmail.com)"
 * @version 03 April 2008
 *
 */
public class InputHandler {
  /** when h is pressed, the high scores will be displayed. */
  public static final char DISPLAY_SCORES = 'h';
  /**when m is pressed the music will be toggled.*/
  public static final char TOGGLE_MUSIC = 'm';
/**space key is pressed the game will start.*/
  public static final char START_GAME = '\u0020';
/**when escape is pressed the game will stop.*/
  public static final char STOP_GAME = 27;
/**when return is pressed the ship will fire.*/
  public static final char FIRE_GUN = '\r';
  /** when a is pressed the ship will turn right.*/
  public static final char     TURN_LEFT = 'a';
/**when s is pressed the ship will turn right.*/
  public static final char     TURN_RIGHT = 's';
/**when [shift] is pressed the ship will use its engine.*/
  public static final char     USE_ENGINE = 15;
/**when d is pressed the shield will be used.*/
  public static final char     USE_SHIELD = 'd';
    //researched ASCII code online and found 32,27,15 the ones im looking for
  /**
   * @return What are the legal keyboard inputs?
   */
  public /*@ pure @*/ char[] legalInputs() {
     //@ assert false;
    final char[] legalInputs = {DISPLAY_SCORES, TOGGLE_MUSIC,
      START_GAME, STOP_GAME, FIRE_GUN, TURN_LEFT,
                                TURN_RIGHT , USE_ENGINE, USE_SHIELD};
    return legalInputs;
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
  /**loop through the array and check if char entered is the same. */
  public /*@ pure @*/ boolean legalInput(final char the_legal_input) {
    //loop through the legal_inputs array
    for (int i = 0; i <= legalInputs().length; i++)
    {
      if (legalInputs()[i] == the_legal_input) {
      /**character typed is same as characters in the input*/
        return true;
      }
    }
    return false; //otherwise return false
  }

  /**
   * Process keyboard input character 'k'.
   */
  //@ requires legal_input(k);
  public void process(final char the_input) {
    final Logger my_log = Logger.getLogger("thrust.input.InputHandler");
     //@ assert false;
    if (legalInput(the_input)) {
      if (the_input == DISPLAY_SCORES) {
        my_log.info("Display scores");
      //display high scores
      } else if (the_input == TOGGLE_MUSIC) {
        my_log.info("TOGGLE MUSIC");
      //toggle music or sound effects
      } else if (the_input == START_GAME)  {
        my_log.info("Start game");
      //start the game
      } else if (the_input == STOP_GAME) {
        my_log.info("Stop Game");
      //stop the game
      } else if (the_input == FIRE_GUN) {
        my_log.info("Fire Gun");
      //Fire the gun
      } else if (the_input == TURN_LEFT) {
      //turn ship left
        my_log.info("Turn Left");
      } else if (the_input == TURN_RIGHT) {
        my_log.info("Turn Right");
      //turn ship right
      } else if (the_input == USE_ENGINE) {
        my_log.info("Use engine");
      } else if (the_input == USE_SHIELD) {
      //use the shield
        my_log.info("use shield");
      } else {
     //this is not a legal input
        my_log.info("This is not a legal input");
      }
    }
  }
}