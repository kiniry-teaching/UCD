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
 * @author Colin Casey (colin.casey@org.com)
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 23 April 2008
 */
public class InputHandler {
  /** Press h to Display the high score table. */
  public static final char DISPLAY_HIGH_SCORES = 'h';
  /** Press m to Toggle between hearing music or sound effects. */
  public static final char TOGGLE_MUSIC_OR_EFFECTS = 'm';
  /** Press n to Start a game. */
  public static final char START_GAME = 'n';
  /** Press q to stop a game. */
  public static final char STOP_GAME = 'q';
  /** Press . to Fire a bullet from the spaceship's gun. */
  public static final char FIRE_GUN = '.';
  /** Press a to Rotate the spaceship counterclockwise. */
  public static final char TURN_LEFT = 'a';
  /** Press s to Rotate the spaceship clockwise. */
  public static final char TURN_RIGHT = 's';
  /** Press , to Use the spaceship's engine to apply thrust forward. */
  public static final char USE_ENGINE = ',';
  /** Press space to Use the spaceships shield
   * to protect itself or to gather fuel. */
  public static final char USE_SHIELD = ' ';

  /**
   * @return What are the legal keyboard inputs?
   */
  public /*@ pure @*/ char[] legal_inputs() {
    final char[] legal_inputs = {DISPLAY_HIGH_SCORES, TOGGLE_MUSIC_OR_EFFECTS,
                                 START_GAME, STOP_GAME, FIRE_GUN, TURN_LEFT,
                                 TURN_RIGHT, USE_ENGINE, USE_SHIELD};
    assert (legal_inputs != null); //@ assert (legal_inputs != null);
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
  public /*@ pure @*/ boolean legal_input(final char the_character) {
    final char[] legal_inputs = legal_inputs();
    assert (legal_inputs != null); //@ assert (legal_inputs != null);
    for (int i = 0; i < legal_inputs.length; i++)  {
      if (legal_inputs[i] == the_character)  {
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
  public void process(final char the_keyboard_input) {
    if (the_keyboard_input == DISPLAY_HIGH_SCORES) {
      //Display high scores
      assert true;
    }   else if (the_keyboard_input == TOGGLE_MUSIC_OR_EFFECTS) {
      //Toggle music or effects on or off
      assert true;
    }   else if (the_keyboard_input == START_GAME) {
      //Start the game
      assert true;
    }   else if (the_keyboard_input == STOP_GAME) {
      //Stop the game
      assert true;
    }   else if (the_keyboard_input == FIRE_GUN) {
      //Fire gun
      assert true;
    }   else if (the_keyboard_input == TURN_LEFT) {
      //Turn ship left
      assert true;
    }   else if (the_keyboard_input == TURN_RIGHT) {
      //Turn ship right
      assert true;
    }   else if (the_keyboard_input == USE_ENGINE) {
      //Use engine
      assert true;
    }   else {
      //Use shield
      assert true;
    }
  }
}
