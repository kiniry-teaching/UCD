/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.input;

/**
 * Processes and delegates each keyboard input received.
 * @author Joe Kiniry (kiniry@acm.org)
 * @author Stephen Murphy
 * @revised 24 April 2008 (smurphy)
 * @version 2 April 2008
 */
public class InputHandler {

  public static final char DISPLAY_HIGH_SCORES = 'h';
  /** Press "h" to display high scores. */
  public static final char TOGGLE_MUSIC_OR_EFFECTS = 'm';
  /** Press "m" to toggle music/effects. */
  public static final char START_GAME = 'p';
  /** Press "p" used here as a toggle, in this case to start the game. */
  public static final char STOP_GAME = 'p';
  /** Press "p" used here as a toggle, in this case to stop the game. */
  public static final char FIRE_GUN = 'z';
  /** Press "z" to fire the ships weapon, producing bullets. */
  public static final char TURN_LEFT = 'a';
  /** Press "a" to direct the ship left. */
  public static final char TURN_RIGHT = 'd';
  /** Press "d" to direct the ship right . */
  public static final char USE_ENGINE = 'w';
  /** Press "w" to use engine..was considering code value for space bar ie. 0x09, possible for other values also maybe? */
  public static final char USE_SHIELD = 's';
  /** Press "s" to use the ship's shield/tractor beam, to protect oneself or to pick up fuel/ or power pod. */
  
  
  /**
   * @return What are the legal keyboard inputs?
   */
  public /*@ pure @*/ char[] legal_inputs() {
    assert false; //@ assert false;
    return null;
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
    final char[] inputs = 
    {DISPLAY_HIGH_SCORES, TOGGLE_MUSIC_OR_EFFECTS, START_GAME, STOP_GAME,FIRE_GUN, TURN_LEFT, TURN_RIGHT, USE_ENGINE, USE_SHIELD };
    // @ assert inputs != null;
  
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
