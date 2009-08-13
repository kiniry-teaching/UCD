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

import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.util.logging.Logger;
import thrust.Main;

/**
 * Processes and delegates each keyboard input received.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class InputHandler extends KeyAdapter {
  /** An unknown character code. */
  public static final char UNKNOWN_CHAR = '\0';
  /** Fill in this comment. */
  public static final char DISPLAY_HIGH_SCORES = (char)KeyEvent.VK_H;
  /** Fill in this comment. */
  public static final char TOGGLE_MUSIC_OR_EFFECTS = (char)KeyEvent.VK_M;
  /** Fill in this comment. */
  public static final char START_GAME = (char)KeyEvent.VK_SPACE;
  /** Fill in this comment. */
  public static final char STOP_GAME = (char)KeyEvent.VK_ESCAPE;
  /** Fill in this comment. */
  public static final char FIRE_GUN = (char)KeyEvent.VK_ENTER;
  /** Fill in this comment. */
  public static final char TURN_LEFT = (char)KeyEvent.VK_A;
  /** Fill in this comment. */
  public static final char TURN_RIGHT = (char)KeyEvent.VK_S;
  /** Fill in this comment. */
  public static final char USE_ENGINE = (char)KeyEvent.VK_SHIFT;
  /** Fill in this comment. */
  public static final char USE_SHIELD = (char)KeyEvent.VK_SPACE;

  /** An information message. */
  private static final String IGNORING_INPUT = "Ignoring input.";

  /**
   * Our tiny state machine encodes whether we are showing
   * the title screen, the high scores, showing a demo of
   * the game, or playing the game.
   */
  private static final byte SHOWING_TITLE_SCREEN = 0,
  SHOWING_HIGH_SCORES = 1, SHOWING_DEMO = 2,
  PLAYING_GAME = 3, EXITING_GAME = 4;

  /**
   * Track if the user wishes to hear music or sound effects.
   * The default is to hear music, and this is toggled when
   * at the high score screen by pushing the 'm' key.
   */
  private transient boolean my_music_rather_than_effects = true;

  /**
   * The game is in one of four states: it is showing the tile
   * screen, showing the high scores (the initial state),
   * showing a demo of the game, playing the game, or exiting
   * the game.
   */
  private transient byte my_game_state = SHOWING_TITLE_SCREEN;
  /*@ private invariant my_game_state == SHOWING_TITLE_SCREEN |
    @                   my_game_state == SHOWING_HIGH_SCORES |
    @                   my_game_state == SHOWING_DEMO |
    @                   my_game_state == PLAYING_GAME |
    @                   my_game_state == EXITING_GAME;
    @ private initially my_game_state == SHOWING_TITLE_SCREEN;
    @*/

  /** @return What are the legal keyboard inputs? */
  public /*@ pure @*/ char[] legal_inputs() {
    final char[] the_legal_inputs = {DISPLAY_HIGH_SCORES,
      TOGGLE_MUSIC_OR_EFFECTS, START_GAME, STOP_GAME,
      FIRE_GUN, TURN_LEFT, TURN_RIGHT, USE_ENGINE,
      USE_SHIELD};
    return the_legal_inputs;
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
    return ((the_character == DISPLAY_HIGH_SCORES) |
        (the_character == TOGGLE_MUSIC_OR_EFFECTS) |
        (the_character == START_GAME) |
        (the_character == STOP_GAME) |
        (the_character == FIRE_GUN) |
        (the_character == TURN_LEFT) |
        (the_character == TURN_RIGHT) |
        (the_character == USE_ENGINE) |
        (the_character == USE_SHIELD));
  }

  /**
   * @param the_keyboard_input ignore all input but for toggle
   * music/sound, start game, and stop game.
   */
  private void process_high_score_screen_input(final char the_keyboard_input) {
    switch (the_keyboard_input) {
      case TOGGLE_MUSIC_OR_EFFECTS:
        my_music_rather_than_effects ^= my_music_rather_than_effects;
        Logger.global.info((my_music_rather_than_effects ?
                           "Playing music." : "Playing effects."));
        break;
      case START_GAME:
      case STOP_GAME:
        process_start_or_stop_game(the_keyboard_input);
      default:
        Logger.global.info(IGNORING_INPUT);
    }
  }

  /**
   * @param the_keyboard_input input relating to starting and stopping
   * the game.
   */
  private void process_start_or_stop_game(final char the_keyboard_input) {
    switch (the_keyboard_input) {
      case START_GAME:
        Logger.global.info("Starting game.");
        my_game_state = PLAYING_GAME;
        break;
      case STOP_GAME:
        Logger.global.info("Exiting game.");
        my_game_state = EXITING_GAME;
        break;
      default:
        Logger.global.info(IGNORING_INPUT);
    }
  }

  /**
   * @param the_keyboard_input ignore all input but for show high scores,
   * start game, and quit game.
   */
  private void process_showing_demo_input(final char the_keyboard_input) {
    switch (the_keyboard_input) {
      case DISPLAY_HIGH_SCORES:
        Logger.global.info("Displaying high scores.");
        my_game_state = SHOWING_HIGH_SCORES;
        break;
      case START_GAME:
      case STOP_GAME:
        process_start_or_stop_game(the_keyboard_input);
      default:
        Logger.global.info(IGNORING_INPUT);
    }
  }

  /**
   * @param the_keyboard_input only process input that has to do with
   * controlling the spaceship or quitting the game.
   */
  private void process_playing_game_input(final char the_keyboard_input) {
    switch (the_keyboard_input) {
      case STOP_GAME:
        Logger.global.info("Stopping game.");
        my_game_state = SHOWING_HIGH_SCORES;
        break;
      case FIRE_GUN:
        Logger.global.info("Firing gun.");
        break;
      case TURN_LEFT:
        Logger.global.info("Turning left.");
        break;
      case TURN_RIGHT:
        Logger.global.info("Turning right.");
        break;
      case USE_ENGINE:
        Logger.global.info("Using engine.");
        break;
      case USE_SHIELD:
        Logger.global.info("Using shield.");
        break;
      default:
        Logger.global.info(IGNORING_INPUT);
    }
  }

  /**
   * Process this keyboard input character.
   * @param the_keyboard_input the input character to process.
   */
  //@ requires legal_input(the_keyboard_input);
  public void process(final char the_keyboard_input) {
    switch (my_game_state) {
      case SHOWING_TITLE_SCREEN:
        // any key will do
        Logger.global.info("Any key was pressed---showing high scores.");
        my_game_state = SHOWING_HIGH_SCORES;
        break;
      case SHOWING_HIGH_SCORES:
        process_high_score_screen_input(the_keyboard_input);
        break;
      case SHOWING_DEMO:
        process_showing_demo_input(the_keyboard_input);
        break;
      case PLAYING_GAME:
        process_playing_game_input(the_keyboard_input);
        break;
      default:
        assert false; //@ assert false;
    }
  }

  /**
   * The main event loop of the game.
   * Repeat the following until the player asks to quit:
   *   show the high score display
   *   wait for input to start the game
   *   create game map and initialize location of all entities
   *   repeat the following until the player is out of lives or asks to quit:
   *      record the current time T
   *      perform a step in the simulation
   *      render all entities
   *      process the next keyboard input
   *      record the current time T'
   *      wait for (1/30th of a second - (T-T'))
   *   remove the game interface
   *   if the player has a new high score
   *     ask them to input their initials
   *     save the new high score
   */
  public void keyPressed(final KeyEvent the_event) {
    final int an_input = (char)the_event.getKeyCode();
    if (Main.INPUT_HANDLER.legal_input((char)an_input)) {
      Main.LOGGER.info("legal input: '" +
                       KeyEvent.getKeyText(an_input) + "'");
      Main.INPUT_HANDLER.process((char)an_input);
    } else {
      Main.LOGGER.info("bad input: '" + KeyEvent.getKeyText(an_input) + "'");
    }
    if (an_input == InputHandler.STOP_GAME) {
      System.exit(0);
    }
    Main.LOGGER.exiting("InputHandler", "main");
  }

  /** {@inheritDoc} */
  public void keyReleased(final /*@ non_null @*/ KeyEvent the_event) {
    // skip
  }

  /** {@inheritDoc} */
  public void keyTyped(final /*@ non_null @*/ KeyEvent the_event) {
    // skip
  }
}
