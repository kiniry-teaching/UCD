package niall;

import java.util.Date;

/**
 * A point-of-sale terminal through which one makes Johnny Card transactions.
 *
 * @author Niall
 *
 */
public class JohnnyRegister {

	private/*@ spec_public non_null@*/JohnnyTrannie[] transactions;

	/**
	 * Default constructor for the register.
	 */
	//@ requires true;
	//@ ensures getTransactions().length == 0;
	//@ assignable \everything;
	public JohnnyRegister() {
		transactions = new JohnnyTrannie[0];
	}

	/**
	 * @return What transactions was this register involved in?
	 */
	//@ requires true;
	//@ ensures \result == transactions;
	public/*@ pure @*/JohnnyTrannie[] getTransactions() {
		return transactions;
	}

	/**
	 * Record a transaction for this amount on that Johnny Card on this date!
	 * @param card execute a purchase for this card.
	 * @param amount for this amount.
	 * @param date on this date.
	 */
	//@ requires card != null;
	//@ requires card.isLocked() == false;
	//@ requires amount <= JohnnyCard.MAX_TX_LIMIT;
	//@ requires amount > 0;
	//@ requires date != null;
	//@ requires card.getCashBalance() >= amount;
	//@ ensures getTransactions().length == \old(transactions.length) + 1;
	//@ ensures card.getCashBalance() == \old(card.getCashBalance()) - amount;
	public void recordTransaction(/*@ non_null*/final JohnnyCard card, final int amount, /*@ non_null*/final Date date) {
		card.updateCashBalance(-amount);
		JohnnyTrannie transaction = new JohnnyTrannie(card, amount, date,
				JohnnyTrannie.PURCHASE_TYPE);
		addTransaction(transaction);
		card.recordTransaction(transaction);
	}

	/**
	 * @param johnnyTrannie add this JohnnyTransaction to the transaction store
	 */
	//@ requires true;
	//@ ensures getTransactions().length == \old(transactions.length) + 1;
	//@ assignable transactions;
	private void addTransaction(/*@ non_null */final JohnnyTrannie johnnyTrannie) {
		int len = getTransactions().length;
		JohnnyTrannie [] tempTrannies = new JohnnyTrannie[len+1];
		//System.arraycopy(transactions, 0, tempTrannies, 0, transactions.length);
		for(int i=0; i<transactions.length; i++){
			tempTrannies[i] = transactions[i];
		}
		tempTrannies[len] = johnnyTrannie;
		transactions = tempTrannies;
	}
}
