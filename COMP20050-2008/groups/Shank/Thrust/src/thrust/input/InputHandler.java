package thrust.input;

/**
 * Processes and delegates each keyboard input received.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 * Edited by Ben Fitzgerald on 07/04/2008
 * Doing the input handlers char values and process method
 */
public class InputHandler {
  /** An unknown character code. */
  private static final char UNKNOWN_CHAR = '\0';
  /** Press (h) to displays the high scores . */
  private static final char DISPLAY_HIGH_SCORES = 'h';
  /** Press (m) to toggle the music or effects . */
  private static final char TOGGLE_MUSIC_OR_EFFECTS = 'm';
  /** Press (space) to start the game. */
  //changed to (s) because it causes a conflict in switch statement in process
  private static final char START_GAME = 's';
  /** Press (escape) to stop the game. */
  private static final char STOP_GAME = (char)27;
  /** Press (return) to fire the ships gun. */
  private static final char FIRE_GUN = '\r';
  /** Press (a) to rotate the ship left. */
  private static final char TURN_LEFT = 'a';
  /** Press (d) to rotate the ship right. */
  private static final char TURN_RIGHT = 'd';
  /** Press (shift) to use the ship's engine. */
  private static final char USE_ENGINE = (char)15;
  /** Press (space) to use the ship's shield. */
  private static final char USE_SHIELD = (char)32;

  /**
   * @return What are the legal keyboard inputs?
   */
  public /*@ pure @*/ char[] legal_inputs() {
    final char[] legal_inputs_array = {DISPLAY_HIGH_SCORES,
                                       TOGGLE_MUSIC_OR_EFFECTS,
                                       START_GAME, STOP_GAME, FIRE_GUN,
                                       TURN_LEFT, TURN_RIGHT,
                                       USE_ENGINE, USE_SHIELD};
    assert legal_inputs_array != null;
    return legal_inputs_array;
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
  public /*@ pure @*/ boolean legal_input(final char the_character)
  {
    final char[] inputs = legal_inputs();
    for (int x = 0; x < inputs.length; x++)
    {
      if (the_character == inputs[x])
      {
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
  public void process(final char the_keyboard_input)
  {
    switch(the_keyboard_input)
    {
      // Change use logging
      // starts Displays high score method called.
      case DISPLAY_HIGH_SCORES: // ("starts Displays high score method");
     // Toggles the music or effects on or off method called.
      case TOGGLE_MUSIC_OR_EFFECTS: //("Toggles the music or effects ");
     // Starts the game method called.
      case START_GAME: //  ("Starts the game");
     // Stops the game method called.
      case STOP_GAME: //  ("Stops the game");
     // fire ships's gun method called.
      case FIRE_GUN: //  ("fire ships's gun");
     // Rotate ship left method called.
      case TURN_LEFT: //  ("Rotate ship left");
        // Rotate ship right method called.
      case TURN_RIGHT: //  ("Rotate ship right");
        // Use ship's engine method called.
      case USE_ENGINE: //  ("Use ship's engine");
     // Use ships shield method called.
      case USE_SHIELD: //  ("Use ships shield");
      default: // ("illegal input");// Unknown char
    }
  }
}
