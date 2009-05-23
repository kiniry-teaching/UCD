package niall;

import java.util.Date;

/**
 * An interactive prompt for exercising the system.  Loops on
 * actions expecting input from a user or a stream-based test driver.
 *
 * @author Niall
 *
 */
public final class Main {

	private /*@ non_null */final JohnnyMachine machine;
	private /*@ non_null */final JohnnyRegister register;
	//@ invariant card.isLocked() == false;
	private /*@ non_null spec_public*/final JohnnyCard card;
	private /*@ non_null */final UserInterface userInterface;

	/** Initialize the Johnny Card system. */
	//@ requires true;
	//@ ensures machine != null;
	//@ ensures register != null;
	//@ ensures card != null;
	//@ ensures userInterface != null;
	//@ assignable \everything;
	private Main() {
		machine = new JohnnyMachine();
		register = new JohnnyRegister();
		card = new JohnnyCard(new JohnnyBank());
		userInterface = new UserInterface();
	}

	/**
	 * Runs an interactive loop exercising a demonstration Johnny Card system.
	 *
	 * @param the_args the arguments of the program.
	 */
	//@ requires true;
	//@ ensures true;
	public static void main(final/* @ non_null @ */String[] theArgs) {
		Main main = new Main();
		main.execute();
	}

	/**
	 * Runs an interactive loop exercising a demonstration Johnny Card system.
	 */
	//@ requires true;
	//@ ensures true;
	private void execute() {
		while (userInterface.isStillRunning() && !card.isLocked()) {
			userInterface.tellUser(String.valueOf(card.getCashBalance()));
			boolean useTerminal = userInterface
					.solicitUserActivity("Would you like to use the terminal or the register? (1) for Terminal or (2) for Register or (3) to quit the system.");

			if(userInterface.isStillRunning()){
				processUserTerminalOrRegisterRequest(useTerminal);
			}
		}
		userInterface.tellUser("The system is finished executing");
	}

	/**
	 * Processes the users request to use the terminal or register.
	 * @param inTerminal is the card in the terminal.
	 */
	//@ requires true;
	//@ ensures true;
	private void processUserTerminalOrRegisterRequest(final boolean inTerminal) {
		if (inTerminal) {
			terminalActivity();
		} else {
			registerActivity();
		}
	}

	/**
	 * Emulates cash terminal activity.
	 */
	//@ requires true;
	//@ ensures true;
	private void terminalActivity() {
		machine.initCardSession();

		if(capturePin()) {
			int amount = userInterface.solicitNumber("How much do you want to add?");
			if(isFundTransferValid(amount)){
					machine.transferFunds(card, amount);
			} else {
				userInterface.tellUser("Those funds cannot be transferred to the card");
			}
		}
	}

	/**
	 * Capture the PIN that the user enters until they enter a valid one.
	 * The user has 3 chances to enter valid PIN, after this time the
	 * card is locked.
	 * @return true if the user enters a valid pin, false otherwise
	 */
	//@ requires true;
	//@ ensures true;
	private boolean capturePin() {
		boolean validPin = false;
		while(isPinStillRequired(validPin)) {
			int pin = userInterface.solicitNumber("Please enter your PIN ... 3 bad attempts and it gets locked!!");
			validPin = machine.validatePin(pin, card);
		}

		return validPin;
	}

	/**
	 * Is a PIN number still required from the user?
	 * @param validPin is the pin number valid
	 * @return is a PIN still required from the user
	 */
	//@ requires true;
	//@ ensures \result == !validPin && !card.isLocked();
	private /*@ pure */boolean isPinStillRequired(final boolean validPin) {
		return !validPin && !card.isLocked();
	}

	/**
	 * @param amount the amount to transfer to the card.
	 * @return is the fund transfer valid for this card and this amount?
	 */
	//@ requires true;
	/*@ ensures \result <==> card.getBankAccount().getBalance() > amount
		&& amount >= 1
		&& card.getCashBalance() + amount <= JohnnyCard.MAX_CASH_BALANCE
		&& card.getCashBalance() + amount >= JohnnyCard.MIN_CASH_BALANCE;
	*/
	private /*@ pure */boolean isFundTransferValid(final int amount){
		return card.getBankAccount().getBalance() > amount
				&& amount >= 1
				&& card.getCashBalance() + amount <= JohnnyCard.MAX_CASH_BALANCE
				&& card.getCashBalance() + amount >= JohnnyCard.MIN_CASH_BALANCE;
	}

	/**
	 * Emulates cash register activity.
	 */
	//@ requires true;
	//@ ensures true;
	private void registerActivity() {
		boolean acceptSale = userInterface
				.solicitUserActivity("Do you accept a sale value of 1? (1) for Yes or (2) for No.");

		if (acceptSale) {
			executeSale(1);
		}
	}

	/**
	 * Execute a sale on the card.
	 */
	//@ requires true;
	//@ ensures true;
	private void executeSale(final int saleValue) {
		if(isValidSaleTransaction(saleValue)){
			register.recordTransaction(card, saleValue, new Date());
		}
		else {
			userInterface.tellUser("That transaction cannot be executed");
		}
	}

	/**
	 * @param saleValue the cash value of the sale transaction.
	 * @return is this sale transaction valid for this card and this amount?
	 */
	//@ requires true;
	/*@ ensures \result <==> JohnnyCard.MIN_CASH_BALANCE <= card.getCashBalance() + saleValue
		&& JohnnyCard.MAX_CASH_BALANCE >= card.getCashBalance() + saleValue
		&& card.getCashBalance() >= saleValue
		&& saleValue <= JohnnyCard.MAX_TX_LIMIT
		&& saleValue > 0;
	*/
	private /*@ pure */boolean isValidSaleTransaction(final int saleValue){
		return JohnnyCard.MIN_CASH_BALANCE <= card.getCashBalance() + saleValue
				&& JohnnyCard.MAX_CASH_BALANCE >= card.getCashBalance() + saleValue
				&& card.getCashBalance() >= saleValue
				&& saleValue <= JohnnyCard.MAX_TX_LIMIT
				&& saleValue > 0;
	}
}
