package thrust.input;
import java.util.logging.Logger;
import java.awt.event.KeyEvent;

/**
 * Processes and delegates each keyboard input received.
 *
 * @author Keith Byrne, Eoghan O'Donovan, Sean Russell (Jar@timbyr.com).
 * @version 2 April 2008
 */
public class InputHandler {
  /** The main menu state. */
  public static final byte MAINMENU = 0;
  /** The high score menu state. */
  public static final byte HIGHSCOREMENU = 1;
  /** The play state. */
  public static final byte PLAY = 2;
  /** The gameover state. */
  public static final byte GAMEOVER = 3;
  /** Character h to display high scores. */
  public static final char HIGH_SCORES = 'h';
  /** Character m switch between music and SFX. */
  public static final char TOGGLE_SOUND = 'm';
  /** Character [space] to start game. */
  public static final char START_GAME = ' ';
  /** Character [escape] to stop game. */
  public static final char STOP_GAME = '\u001B';
  /** Character [enter] to fire gun. */
  public static final char FIRE_GUN = '\n';
  /** Character a to turn left. */
  public static final char TURN_LEFT = 'a';
  /** Character s to turn right. */
  public static final char TURN_RIGHT = 's';
  /** Character [shift] to thrust. */
  public static final char USE_ENGINE = KeyEvent.VK_SHIFT;
  /** Character [space] to turn on shield/pickup. */
  public static final char USE_SHIELD = ' ';
  /** Logger for input package. */
  protected static final Logger LOG = Logger.getLogger("Input");

  /*
   * @ ensures \result !=null;
   */
  /**
   * @return What are the legal keyboard inputs?
   */
  public final/* @ pure @ */char[] legalInputs() {
    final char[] inputs =
    {HIGH_SCORES, TOGGLE_SOUND, START_GAME, STOP_GAME,
     FIRE_GUN, TURN_LEFT, TURN_RIGHT, USE_ENGINE,
     USE_SHIELD };
    // @ assert inputs != null;
    return inputs;
  }

  /*
   * @ ensures \result <==> (theCharacter == HIGH_SCORES) |
   * @                      (theCharacter ==TOGGLE_SOUND) |
   * @                      (theCharacter == START_GAME) |
   * @                      (theCharacter == STOP_GAME) |
   * @                      (theCharacter == FIRE_GUN) |
   * @                      (theCharacter == TURN_LEFT) |
   * @                      (theCharacter == TURN_RIGHT) |
   * @                      (theCharacter == USE_ENGINE) |
   * @                      (theCharacter == USE_SHIELD);
   */
  /**
   * @return Is this character a legal keyboard input?
   * @param theCharacter
   *          the character to check.
   */
  public final/* @ pure @ */boolean legalInput(final char the_character) {
    boolean exit = false;
    for (int i = 0; i < legalInputs().length; ++i) {
      if (legalInputs()[i] == the_character) {
        exit = true;
      }
    }
    return exit;
  }

  /**
   * Process this keyboard input character.
   *
   * @param theKeyboardInput
   *          the input character to process.
   */
  // @ requires legalInput(the_key_input);
  public void process(final char the_key_input) {
    // @ assert true;
    switch (thrust.Main.GAMESTATE.get_state()) {
      case MAINMENU:
        processMenu(the_key_input);
        break;
      case PLAY:
        processPlay(the_key_input);
        break;
      case HIGHSCOREMENU:
        processHigh(the_key_input);
        break;
      case GAMEOVER:
        processOver(the_key_input);
        break;
      default:
        break;
    }
    switch (thrust.Main.GAMESTATE.get_state()) {
      case MAINMENU:
        LOG.info("Main menu");
        break;
      case PLAY:
        LOG.info("Play");
        break;
      case HIGHSCOREMENU:
        LOG.info("High scores");
        break;
      case GAMEOVER:
        LOG.info("Game over");
        break;
      default:
        break;
    }
  }

  /**
   * Process this keyboard input character.
   *
   * @param theKeyboardInput
   *          the input character to process.
   */
  // @ requires legalInput(the_key_input);
  public void processMenu(final char the_key_input) {
    switch (the_key_input) {
      case HIGH_SCORES:
        thrust.Main.GAMESTATE.set_state(HIGHSCOREMENU);
        break;
      case TOGGLE_SOUND:
        LOG.info("Toggle Sound");
        if (thrust.Main.MUSIC.playing()) {
          thrust.Main.MUSIC.stop();
        } else {
          thrust.Main.MUSIC.start();
        }
        break;
      case START_GAME:
        thrust.Main.GAMESTATE.set_state(PLAY);
        break;
      case STOP_GAME:
        System.exit(0);
      default:
        break;
    }
  }

  /**
   * Process this keyboard input character.
   *
   * @param theKeyboardInput
   *          the input character to process.
   */
  // @ requires legalInput(the_key_input);
  public void processPlay(final char the_key_input) {
    switch (the_key_input) {
      case STOP_GAME:
        thrust.Main.GAMESTATE.set_state(MAINMENU);
        break;
      case FIRE_GUN:
        LOG.info("Fire the Gun");
        break;
      case TURN_LEFT:
        LOG.info("Turn left");
        break;
      case TURN_RIGHT:
        LOG.info("Turn right");
        break;
      case USE_ENGINE:
        LOG.info("Engage thrust");
        break;
      case USE_SHIELD:
        LOG.info("Engage shield/pickup");
      default:
        break;
    }
    thrust.Main.my_check = false;
  }

  /**
   * Process this keyboard input character.
   *
   * @param theKeyboardInput
   *          the input character to process.
   */
  // @ requires legalInput(the_key_input);
  public void processHigh(final char the_key_input) {
    switch (the_key_input) {
      case STOP_GAME:
        thrust.Main.GAMESTATE.set_state(MAINMENU);
        break;
      default:
        break;
    }
  }
  /**
   * Process this keyboard input character.
   *
   * @param theKeyboardInput
   *          the input character to process.
   */
  // @ requires legalInput(the_key_input);
  public void processOver(final char the_key_input) {
    switch (the_key_input) {
      case STOP_GAME:
        thrust.Main.GAMESTATE.set_state(MAINMENU);
        break;
      case START_GAME:
        thrust.Main.GAMESTATE.set_state(MAINMENU);
        break;
      default:
        break;
    }
  }
}
