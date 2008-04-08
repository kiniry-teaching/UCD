package thrust.input;
import java.awt.event.KeyEvent;

/**
 * Processes and delegates each keyboard input received.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class InputHandler {
  /** Displays the high score when the h button is pressed. */
  public static final char DISPLAY_HIGH_SCORES = KeyEvent.VK_H;
  /** Toggles music on and off when the m button is pressed. */
  public static final char TOGGLE_MUSIC_OR_EFFECTS = KeyEvent.VK_M;
  /** Starts the game when the [space] button is pressed. */
  public static final char START_GAME = KeyEvent.VK_SPACE;
  /** Quits the game when the [escape] button is pressed. */
  public static final char STOP_GAME = KeyEvent.VK_ESCAPE;
  /** Fires the gun of the spaceship when the [enter] button is pressed. */
  public static final char FIRE_GUN = KeyEvent.VK_ENTER;
  /** Rotates the spaceship left when a button is pressed. */
  public static final char TURN_LEFT = KeyEvent.VK_A;
  /**Rotates the spaceship right when s button is pressed. */
  public static final char TURN_RIGHT = KeyEvent.VK_S;
  /** Causes spaceship to move forward when [shift] button is pressed. */
  public static final char USE_ENGINE = KeyEvent.VK_SHIFT;
  /** Activates shield when [space] button is pressed. */
  public static final char USE_SHIELD = KeyEvent.VK_SPACE;


  /**
   * @return What are the legal keyboard inputs?
   */
  public final /*@ pure @*/ char[] legal_inputs() {
    final char[] inputs = {DISPLAY_HIGH_SCORES, TOGGLE_MUSIC_OR_EFFECTS,
                           START_GAME, STOP_GAME, FIRE_GUN, TURN_LEFT,
                           TURN_RIGHT, USE_ENGINE, USE_SHIELD};
    /*inputs[0] = DISPLAY_HIGH_SCORES;
    inputs[1] = TOGGLE_MUSIC_OR_EFFECTS;
    inputs[2] = START_GAME;
    inputs[3] = STOP_GAME;
    inputs[4] = FIRE_GUN;
    inputs[5] = TURN_LEFT;
    inputs[6] = TURN_RIGHT;
    inputs[7] = USE_ENGINE;
    inputs[8] = USE_SHIELD;*/

    return inputs;
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

   /** Determines whether or not the input is a legal one.
   * @return Is the input one which has been listed as a legal one?
   * @param the_character is the input entered by the user.
   */
  public final /*@ pure @*/ boolean legal_input(final char the_character) {
    boolean quit = false;
    final char[] inputs = legal_inputs();
    for (int i = 0; i < inputs.length; i++) {
      if (the_character == inputs[i]) {
        quit = true;
      }
    }
    return quit;
  }

  /**
   * Process this keyboard input character.
   * @param the_keyboard_input the input character to process.
   */
  //@ requires legal_input(the_keyboard_input);
  public final void process(final char the_keyboard_input) {

    if (the_keyboard_input == KeyEvent.VK_H) {
      System.out.print("Should call the DISPLAY_HIGH_SCORES method");
    }
    if (the_keyboard_input == KeyEvent.VK_M) {
      System.out.print("Should call the TOGGLE_MUSIC_OR_EFFECTS method");
    }
    if (the_keyboard_input == KeyEvent.VK_SPACE) {
      System.out.print("Should call the START_GAME method");
    }
    if (the_keyboard_input == KeyEvent.VK_ESCAPE) {
      System.out.print("Should call the STOP_GAME method");
    }
    if (the_keyboard_input == KeyEvent.VK_ENTER) {
      System.out.print("Should call the FIRE_GUN method");
    }
    if (the_keyboard_input == KeyEvent.VK_A) {
      System.out.print("Should call the TURN_LEFT method");
    }
    if (the_keyboard_input == KeyEvent.VK_S) {
      System.out.print("Should call the TURN_RIGHT method");
    }
    if (the_keyboard_input == KeyEvent.VK_SHIFT) {
      System.out.print("Should call the USE_ENGINE method");
    }
    if (the_keyboard_input == KeyEvent.VK_SPACE) {
      System.out.print("Should call the USE_SHIELD method");
    }

    assert false; //@ assert false;
  }
}
