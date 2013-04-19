package niall;

/**
 * A terminal for using Johnny Cards. Adds cash to a Johnny Card.
 * Used for managing funds of a Johnny Card.
 * @author ralphhyland
 */
public class JohnnyMachine {

	private static final int BAD_PIN_ATTEMPTS = 3;
	private static final int DEFAULT_BAD_PIN_ATTEMPTS = 0;

	private /*@ spec_public @*/int badPinAttemptsForCurrentCard = DEFAULT_BAD_PIN_ATTEMPTS;

	/**
	 * @param johnnyCard the Johnny card associated with the bank account.
	 * @return How much moola do I have in my bank account?
	 */
	//@ requires johnnyCard != null;
	//@ requires johnnyCard.getBankAccount() != null;
	//@ ensures \result == johnnyCard.getBankAccount().getBalance();
	public/*@ pure @*/int getBalance(final /*@ non_null */JohnnyCard johnnyCard) {
		return johnnyCard.getBankAccount().getBalance();
	}

	/**
	 * @param johnnyCard The JohnnyCard who's balance we want to obtain.
	 * @return How much moola do I have on my Johnny Card?
	 */
	//@ requires johnnyCard != null;
	//@ ensures \result == johnnyCard.getCashBalance();
	public/*@ pure @*/ int getJohnnyCardBalance(final /*@ non_null */JohnnyCard johnnyCard) {
		return johnnyCard.getCashBalance();
	}

	/**
	 * @param johnnyCard Lock the Johnny Card!
	 */
	//@ requires johnnyCard != null;
	//@ requires !johnnyCard.isLocked();
	//@ ensures johnnyCard.isLocked();
	public void lockJohnnyCard(final /*@ non_null */JohnnyCard johnnyCard) {
		johnnyCard.setLocked(true);
	}

	/**
	 * Transfer this amount from Johnny Bank to Johnny Card!
	 * @param johnnyCard the johnny card to transfer amount to
	 * @param amount the amount to transfer from the johnny bank to the johnny card
	 */
	//@ requires johnnyCard != null;
	//@ requires !johnnyCard.isLocked();
	//@ requires johnnyCard.getBankAccount() != null;
	//@ requires johnnyCard.getBankAccount().getBalance() >= amount;
	//@ requires amount >= 1;
	//@ requires johnnyCard.getCashBalance() + amount <= JohnnyCard.MAX_CASH_BALANCE;
	//@ requires johnnyCard.getCashBalance() + amount >= JohnnyCard.MIN_CASH_BALANCE;
	public void transferFunds(final /*@ non_null */JohnnyCard johnnyCard, final int amount) {
		JohnnyBank johnnyBank = johnnyCard.getBankAccount();
		johnnyBank.updateBalance(-amount);
		johnnyCard.updateCashBalance(amount);
	}

	/**
	 * @param theBadPinAttempts Set the Bad PIN attempts to this value!
	 */
	//@ requires true;
	//@ ensures getBadPinAttemptsForCurrentCard() == theBadPinAttempts;
	//@ assignable badPinAttemptsForCurrentCard;
	private void setBadPinAttemptsForCurrentCard(final int theBadPinAttempts) {
		badPinAttemptsForCurrentCard = theBadPinAttempts;
	}

	/**
	 * @return theBadPinAttempts for the current card
	 */
	//@ requires true;
	//@ ensures \result == badPinAttemptsForCurrentCard;
	private /*@ pure spec_public*/int getBadPinAttemptsForCurrentCard() {
		return badPinAttemptsForCurrentCard;
	}

	/**
	 * Is this PIN valid for this card?
	 * @param thePIN the pin to check
	 * @param card the card on which the pin should be checked
	 * @return true if the pin is correct, false otherwise
	 */
	//@ requires true;
	//@ requires !card.isLocked();
	//@ ensures \result == false && getBadPinAttemptsForCurrentCard() >= BAD_PIN_ATTEMPTS ==> card.isLocked();
	public boolean validatePin(final int thePIN, final /*@ non_null */JohnnyCard card) {
		boolean validPin = card.getBankAccount().validatePin(thePIN);
		if(!validPin){
			setBadPinAttemptsForCurrentCard(getBadPinAttemptsForCurrentCard() + 1);
			if(getBadPinAttemptsForCurrentCard() >= BAD_PIN_ATTEMPTS) {
				lockJohnnyCard(card);
			}
		}

		return validPin;
	}
	/**
	 * Initialize a new session when a card is inserted into the machine!
	 */
	//@ requires true;
	//@ ensures getBadPinAttemptsForCurrentCard() == DEFAULT_BAD_PIN_ATTEMPTS;
	//@ assignable badPinAttemptsForCurrentCard;
	public void initCardSession(){
		setBadPinAttemptsForCurrentCard(DEFAULT_BAD_PIN_ATTEMPTS);
	}
}

