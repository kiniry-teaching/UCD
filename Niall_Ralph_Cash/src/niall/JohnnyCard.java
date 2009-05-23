package niall;


/**
 * The Johnny Card is a digital cash card which uses a flash filesystem to store
 * virtual cash for connectionless point-of-sale transactions.
 * @author Niall
 */
public class JohnnyCard {

	public static final int MAX_CASH_BALANCE = 500;
	public static final int MIN_CASH_BALANCE = 0;
	public static final int MAX_TX_LIMIT = 500;

	//@ invariant getCashBalance() <= MAX_CASH_BALANCE;
	//@ invariant getCashBalance() >= MIN_CASH_BALANCE;
	private/*@ spec_public @*/int cashBalance;

	private/*@ spec_public non_null @*/ final JohnnyBank bankAccount;

	private/*@ spec_public non_null@*/JohnnyTrannie[] transactions;

	private/*@ spec_public @*/boolean locked;

	/**
	 * Initialize the card and associate the card with this bank account!
	 * @param theBankAccount the bank account which the card should be associated with.
	 */
	//@ requires true;
	//@ ensures getBankAccount() == theBankAccount;
	//@ ensures getCashBalance() == MIN_CASH_BALANCE;
	//@ ensures getTransactions().length == 0;
	//@ ensures isLocked() == false;
	//@ assignable \everything;
	public JohnnyCard(final /*@ non_null */JohnnyBank theBankAccount) {
		bankAccount = theBankAccount;
		cashBalance = MIN_CASH_BALANCE;
		transactions = new JohnnyTrannie[0];
		locked = false;
	}

	/**
	 * @return How much cash is on this card?
	 */
	//@ requires true;
	//@ ensures \result == cashBalance;
	public/*@ pure @*/int getCashBalance() {
		return cashBalance;
	}

	/**
	 * @return What transactions was this card involved in?
	 */
	//@ requires true;
	//@ ensures \result == transactions;
	public/*@ pure @*/JohnnyTrannie[] getTransactions() {
		return transactions;
	}

	/**
	 * @return What is the lock status of this card?
	 */
	//@ requires true;
	//@ ensures \result == locked;
	public/*@ pure @*/boolean isLocked() {
		return locked;
	}

	/**
	 * @return What is the bank account associated with this card?
	 */
	//@ requires true;
	//@ ensures \result == bankAccount;
	public/*@ pure @*/JohnnyBank getBankAccount() {
		return bankAccount;
	}

	/**
	 * @param theCashValue Change the amount of cash on this card by this much!
	 */
	//@ requires MIN_CASH_BALANCE <= getCashBalance() + theCashValue;
	//@ requires MAX_CASH_BALANCE >= getCashBalance() + theCashValue;
	//@ ensures getCashBalance() == \old(getCashBalance()) + theCashValue;
	//@ ensures getCashBalance() >= MIN_CASH_BALANCE;
	//@ ensures getCashBalance() <= MAX_CASH_BALANCE;
	//@ assignable cashBalance;
	public void updateCashBalance(final int theCashValue) {
		cashBalance += theCashValue;
	}

	/**
	 * @param theTransaction Record this transaction on the card!
	 */
	//@ requires theTransaction != null;
	//@ ensures getTransactions().length == \old(transactions.length) + 1;
	//@ ensures getTransactions()[transactions.length - 1] == theTransaction;
	//@ assignable transactions;
	public void recordTransaction(final /*@ non_null */JohnnyTrannie theTransaction) {
		int len = getTransactions().length;
		JohnnyTrannie [] tempTrannies = new JohnnyTrannie[len+1];
		//System.arraycopy(transactions, 0, tempTrannies, 0, transactions.length);
		for(int i=0; i<transactions.length; i++){
			tempTrannies[i] = transactions[i];
		}
		tempTrannies[len] = theTransaction;
		transactions = tempTrannies;
	}

	/**
	 * @param theLockStatus Set the lock status to this!
	 */
	//@ requires true;
	//@ ensures isLocked() == theLockStatus;
	//@ assignable locked;
	public void setLocked(final boolean theLockStatus) {
		locked = theLockStatus;
	}
}
