package niall;

import java.util.Date;

/**
 * A transaction on a Johnny Card.
 *
 * @author Niall
 *
 */
public class JohnnyTrannie {

	public static final char PURCHASE_TYPE = 'P';
	public static final char UPLOAD_TYPE = 'U';

	//@ invariant getTransactionType() == PURCHASE_TYPE || getTransactionType() == UPLOAD_TYPE;
	private final /*@ spec_public @*/ char transactionType;
	private final /*@ non_null spec_public @*/ JohnnyCard card;

	private final /*@ non_null spec_public @*/ Date date;

	private final /*@ spec_public @*/ int amount;

	/**
	 * @return What is the date of this transaction?
	 */
	//@ requires true;
	//@ ensures \result == date;
	public/*@ pure @*/Date getDate() {
		return date;
	}

	/**
	 * @return What is the amount of this transaction?
	 */
	//@ requires true;
	//@ ensures \result == amount;
	public final/*@ pure @*/int getAmount() {
		return amount;
	}

	/**
	 * @return Which card is associated with this transaction?
	 */
	//@ requires true;
	//@ ensures \result == card;
	public/*@ pure @*/JohnnyCard getCard() {
		return card;
	}

	/**
	 * @return What type of transaction is this (purchase or upload funds)?
	 */
	//@ requires true;
	//@ ensures \result == transactionType;
	public/*@ pure @*/char getTransactionType() {
		return transactionType;
	}

	/**
	 * Create a transaction for this card, on this date, for this amount and for
	 * this type of transaction!
	 * @param theCard The card to associate with this transaction.
	 * @param theAmount The amount to associate with this transaction.
	 * @param theDate The date to associate with this transaction.
	 * @param transType The transaction type to associate with this
	 *            transaction.
	 */
	//@ requires theCard != null;
	//@ requires theDate != null;
	//@ requires transType == PURCHASE_TYPE || transType == UPLOAD_TYPE;
	//@ ensures getCard() == theCard;
	//@ ensures getAmount() == theAmount;
	//@ ensures getDate() == theDate;
	//@ ensures getTransactionType() == transType;
	//@ assignable \everything;
	public JohnnyTrannie(/*@ non_null */final JohnnyCard theCard, final int theAmount,
			/*@ non_null */final Date theDate, final char transType){
		card = theCard;
		amount = theAmount;
		date = theDate;
		transactionType = transType;
	}
}
