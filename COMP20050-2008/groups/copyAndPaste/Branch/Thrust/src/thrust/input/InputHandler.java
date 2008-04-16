package thrust.input;

/**
 * Processes and delegates each keyboard input received.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 * @revised 04/04/08 Patrick Nevin: 06754155
 *                   Ciaran Flynn: 06516564
 *                   Robert Plunkett: 06038883
 * The three of us contributed equally to the implementation of the
 * keyboard input and handler classes so far
 *
 * We have also started to implement the audio aspect of the project.
 */
public class InputHandler {

	/** Press h to Display High Score.*/
	public static final char DISPLAY_HIGH_SCORES = 'h';
	/** Press m to Toggle Music Or Effect.*/
	public static final char TOGGLE_MUSIC_OR_EFFECTS = 'm';
	/**Press [space] to Start Game.*/
	public static final char START_GAME = ' ';
	/** Press [Esc] to Stop Game.*/
	public static final char STOP_GAME = 27;
	/**Press [Return] to Fire Gun.*/
	public static final char FIRE_GUN = '\r';
	/**Press a to Turn Left.*/
	public static final char TURN_LEFT = 'a';
	/**Press s to Turn Right.*/
	public static final char TURN_RIGHT = 's';
	/**Press shift to Use Engine.*/
	public static final char USE_ENGINE = 16;
	/**Press [Space] to Use Shield.*/
	public static final char USE_SHIELD = ' ';

	//please see comment in process() method....
	public KeyBoardInput inputType;

	/**
	 * @return What are the legal keyboard inputs?
	 */
	public/*@ pure @*/char[] legal_inputs() {
		//any array of char's
		final char[] legal_inputs = { DISPLAY_HIGH_SCORES,
				TOGGLE_MUSIC_OR_EFFECTS, START_GAME, STOP_GAME, FIRE_GUN,
				TURN_LEFT, TURN_RIGHT, USE_ENGINE, USE_SHIELD };
		//return the array
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
	public/*@ pure @*/boolean legal_input(char the_character) {

		char[] legals = legal_inputs();
		for (int i = 0; i <= legals.length; i++) {
			if (legals[i] == the_character) {
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
	public void process(char the_keyboard_input) {

		/** Need a boolean condition to determine if the
		 * game is on or off i.e.,
		 * boolean gameOn = false;
		 * we have yet to determine where we will place this,
		 * we are aware the this boolean has to be placed outside
		 * of this method and class, but use it here as a preliminary
		 * to aid our understanding of the implementation
		 */
		boolean gameOn = false;

		/**
		 * Also we need to determine how to deal with the_keyboard input,
		 * as a temporary solution we've created an new polymorphic instance of
		 * KeyboardInut: "inputType" to reference the type of KeyBoardInput
		 * associated with the input the_keyboard_input
		 */

		switch (the_keyboard_input) {
		case DISPLAY_HIGH_SCORES:
			inputType = new DisplayHighScores();
			break;
		case TOGGLE_MUSIC_OR_EFFECTS:
			inputType = new ToggleMusicOrEffects();
			break;
		case STOP_GAME:
			gameOn = false;
			inputType = new StopGame();
			break;
		case FIRE_GUN:
			inputType = new FireGun();
			break;
		case TURN_LEFT:
			inputType = new TurnLeft();
			break;
		case TURN_RIGHT:
			inputType = new TurnRight();
			break;
		case USE_ENGINE:
			inputType = new UseEngine();
			break;
		default:/**do nothing*/
		}
		//char [space] is overloaded and has two associated behaviours
		//if the game is not on, start the game when [space] pressed
		if (the_keyboard_input == ' '/**START_GAME*/
			&& !gameOn) {
			inputType = new StartGame();
			gameOn = true;
		}
		//otherwise if the game is not on use shield when [space] pressed
		else if (the_keyboard_input == ' '/**USE_SHIELD*/
			&& gameOn) {
			inputType = new UseShield();
		}
	}
}