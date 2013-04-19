package niall;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * This class is used to send/receive information for the user of the Johnny
 * Cash System.
 * @author Niall
 *
 */
public final class UserInterface {

	private static /*@ non_null */final Logger LOG = Logger.getAnonymousLogger();
	private final /*@ non_null */BufferedReader reader;
	private /*@ spec_public */boolean stillRunning;

	private static final int OPTION_ONE = 1;
	private static final int OPTION_TWO = 2;
	private static final int OPTION_THREE = 3;

	/**
	 * Default constructor.
	 */
	//@ requires true;
	//@ ensures stillRunning == true;
	//@ ensures reader != null;
	//@ assignable \everything;
	public UserInterface(){
		stillRunning = true;
		reader = new BufferedReader(new InputStreamReader(System.in));
	}

	/**
	 * @param message Prompt the user for card usage.
	 * @return What does the user want to do with their card?
	 */
	//@ requires true;
	//@ ensures true;
	public boolean solicitUserActivity(/* @ non_null @ */final String message) {
		boolean result = false;
		int userChoice = -1;
		while (userChoice == -1) {
			tellUser(message);
			try {
				String userInput = reader.readLine();
				if (userInput != null) {
					userChoice = Integer.parseInt(userInput);
					if(isUserChoiceValid(userChoice)) {
						result = processUserChoice(userChoice);
					} else {
						userChoice = -1;
					}
				}
			} catch (NumberFormatException nfe) {
				tellUser("That is not a number");
			} catch (IOException e) {
				logError("IOError", e);
			}
		}

		return result;
	}

	/**
	 * Is the user choice a valid one?
	 * @param userChoice the user choice.
	 * @return did the user enter a valid selection?
	 */
	//@ requires true;
	//@ ensures \result == true ==> userChoice == OPTION_ONE || userChoice == OPTION_TWO || userChoice == OPTION_THREE;
	private /*@ pure */boolean isUserChoiceValid(final int userChoice){
		return userChoice == OPTION_ONE || userChoice == OPTION_TWO || userChoice == OPTION_THREE;
	}

	/**
	 * Process the users choice.
	 * @param userChoice the users choice.
	 * @return indicator to see if the user selected option one or two.
	 */
	//@ requires true;
	//@ ensures true;
	//@ assignable stillRunning;
	private boolean processUserChoice(final int userChoice) {
		boolean result = false;
			switch (userChoice) {
			case OPTION_ONE:
				result = true;
				break;
			case OPTION_THREE:
				stillRunning = false;
				break;
			default:
				break;
			}
		return result;
	}

	/**
	 * @param message Prompt the user for the amount.
	 * @return How much money should be added to the card?
	 */
	//@ requires true;
	//@ ensures true;
	public int solicitNumber(/* @ non_null @ */final String message) {
		int returnValue = -1;
		String userInput;
		while(returnValue == -1){
			tellUser(message);
			try {
				userInput = reader.readLine();
				returnValue = processNumber(userInput);
			} catch (IOException e) {
				logError("IOError", e);
			}
		}
		return returnValue;
	}

	/**
	 * Process a number that the user types in.
	 * @param userInput the user input
	 * @return the number that the user typed in
	 */
	//@ requires true;
	//@ ensures true;
	private int processNumber(/* @ non_null @ */final String userInput) {
		int returnValue = -1;
		try{
			if (userInput != null) {
				returnValue = Integer.parseInt(userInput);
			}
		} catch (NumberFormatException nfe) {
			tellUser("That is not a number");
		}
		return returnValue;
	}

	/**
	 * @param message Tell the user something.
	 */
	//@ requires true;
	//@ ensures true;
	public void tellUser(/* @ non_null @ */final String message) {
		LOG.info(message);
	}

	/**
	 * @return Is the UserInterface still running?
	 */
	//@ requires true;
	//@ ensures \result == stillRunning;
	public /*@ pure */boolean isStillRunning(){
		return stillRunning;
	}

	/**
	 * Log an error.
	 * @param errorMessage the error message
	 * @param throwable the throwable
	 */
	//@ requires true;
	//@ ensures true;
	private void logError(/* @ non_null @ */final String errorMessage, /* @ non_null @ */final Throwable throwable) {
		LOG.log(Level.SEVERE, errorMessage, throwable);
	}
}
