package johnnycash;

import java.util.Date;

/** JOHNNY_TRANSATION is a transaction where a user adds money to a JOHNNY card
 * or removes it.
 * @author Home
 */
public class JohnnyTransaction {
  
  /** Amount must be greater than 0 and less then 500 euro. */
  private static final int MAX_AMOUNT = 500;
  /** Amount must be greater than 0 and less then 500 euro. */
  private static final int MIN_AMOUNT = 0;

  /** The id of the card used to make this transaction. */
  private /*@ spec_public */ int johnnyCardId;
  /** The date this transaction occurred at. */
  private /*@ spec_public */ Date transactionDate = new Date();
  /** The Amount of this transaction. */
  private /*@ spec_public */ int transactionAmount;
  /** The Terminal Id of the machine that made this transaction. */
  private /*@ spec_public */int terminalId;

  /** Public constructor, sets up defaults. */
  public JohnnyTransaction() {
    terminalId = 1;
    transactionAmount = 1;
    johnnyCardId = 1;
    transactionDate = new Date();
  }
  
  
  /** "Amount must be greater than 0 and less then 500 Euro." */
  /*@ invariant transactionAmount >= MIN_AMOUNT;
      invariant transactionAmount <= MAX_AMOUNT; */

  /** @return "What is the JOHNNY_CARD id?",*/
  //@ requires true;
  //@ ensures \result == johnnyCardId;
  public final /*@ pure */ int getJohnnyCardId() {
    return johnnyCardId;
  }

  /** @param theJohnnyCardId Change the JohnnyCard 
   *  id in this JohnnyTransaction.*/
  //@ requires johnnyCardId > 0;
  //@ assignable johnnyCardId;
  //@ ensures getJohnnyCardId() == theJohnnyCardId;
  public final void setJohnnyCardId(final int theJohnnyCardId) {
    johnnyCardId = theJohnnyCardId;
  }

  /** @return What is the created date of this JohnnyTransaction?*/
  //@ requires true;
  //@ ensures \result == transactionDate;
  public final /*@ pure */ Date getTransactionDate() {
    return transactionDate;
  }

  /** @param theDate Change the created date of this JohnnyTransaction.*/
  //@ requires transactionDate != null;
  //@ assignable transactionDate;
  //@ ensures getTransactionDate() == theDate;
  public final void setTransactionDate(final Date theDate) {
    transactionDate = theDate;
  }

  /**@return How much is the amount of this JohnnyTransaction?*/
  //@ requires true;
  //@ ensures \result == transactionAmount;
  public final /*@ pure */int getTransactionAmount() {
    return transactionAmount;
  }

  /**@param theAmount Change the amount of this JohnnyTransaction.*/
  //@ requires theAmount >= MIN_AMOUNT;
  //@ requires theAmount <= MAX_AMOUNT;
  //@ assignable transactionAmount;
  //@ ensures getTransactionAmount() == theAmount; 
  public final void setTransactionAmount(final int theAmount) {
    //@assert theAmount >= MIN_AMOUNT;
    assert theAmount >= MIN_AMOUNT;
    //@assert theAmount <= MAX_AMOUNT;
    assert theAmount <= MAX_AMOUNT;
    if (theAmount >= MIN_AMOUNT && theAmount <= MAX_AMOUNT) {
      transactionAmount = theAmount;
    }
  }

  /** @return What is the terminal id of this JohnnyTransaction?*/
  //@ requires true;
  //@ ensures \result == terminalId;
  public final /*@ pure */ int getTerminalId() {
    return terminalId;
  }

  /**@param theTerminalId Change the terminal id of this JohnnyTransaction.*/
  //@ requires true;
  //@ assignable terminalId;
  //@ ensures getTerminalId() == theTerminalId;
  public final void setTerminalId(final int theTerminalId) {
    terminalId = theTerminalId;
  }

}
