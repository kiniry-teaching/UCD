package niall;

/**
 * The bank with which a Johnny card is associated.
 * @author Niall
 */
public class JohnnyBank {

	private static final int DEFAULT_BALANCE = 2000;
	private static final int DEFAULT_PIN = 9999;

	private/*@ spec_public @*/int balance;
	private final /*@ spec_public@*/int pin;

	/**
	 * JohnnyBank default constructor.
	 */
	//@ ensures getPin() == DEFAULT_PIN;
	//@ ensures getBalance() == DEFAULT_BALANCE;
	public JohnnyBank() {
		pin = DEFAULT_PIN;
		balance = DEFAULT_BALANCE;
	}

	/**
	 * @return How much money is available in this account?
	 */
	//@ requires true;
	//@ ensures \result == balance;
	public final /*@ pure  @*/int getBalance() {
		return balance;
	}

	/**
	 * @return What is the PIN of this account?
	 */
	//@ requires true;
	//@ ensures \result == pin;
	private/*@ pure spec_public@*/int getPin() {
		return pin;
	}

	/**
	 * @param thePIN Is this PIN entry valid for this account?
	 * @return returns true if the PIN entry is valid (false otherwise)
	 */
	//@ requires true;
	//@ ensures \result == false ==> getPin() != thePIN && \result == true ==> getPin() == thePIN;
	public /*@ pure */boolean validatePin(final int thePIN) {
		return getPin() == thePIN;
	}

	/**
	 * @param theAmount Change the amount in the account by this much!
	 */
	//@ requires true;
	//@ ensures getBalance() == \old(balance) + theAmount;
	//@ assignable balance;
	public final void updateBalance(final int theAmount) {
		balance = balance + theAmount;
	}
}
