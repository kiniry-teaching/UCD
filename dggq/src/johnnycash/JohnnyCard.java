package johnnycash;

/**
 * JohnnyCard is digital card system that stores digital cash. for connection
 * less transactions
 */
public class JohnnyCard {

  /** The amount of cash on a JohnnyCard cannot be greater 500 Euro. */
  private static final int MAX_AMOUNT = 500;
  /** There are only a max of five JohnnyTransactions saved on this card. */
  private static final int MAX_TRANSACTIONS = 5;
  /** You cannot have a negative amount on a JohnnyCard. */
  private static final int MIN_AMOUNT = 0;

  /** The Johnny card Id. */
  private /*@ spec_public */ int johnnyCardId;
  /** The balance on this johnnyCard. */
  private /*@ spec_public */ int balance;
  /** The five last transactions against this card. */
  private /*@ spec_public */ JohnnyTransaction[] transactions 
    = new JohnnyTransaction[0];

  /** The lock state is LOCKED or UNLOCKED. */
  private/*@ spec_public */boolean locked;

  /** Default constructor for JohnnyCard. */
  public JohnnyCard() {
    johnnyCardId = 0;
    balance = 0;
    transactions = new JohnnyTransaction[0];
  }
  
  /** The amount of cash on a JohnnyCard cannot be greater 500 Euro." */
  /*@ invariant balance <= MAX_AMOUNT; */

  /** There are only a max of five JohnnyTransactions saved on this card. */
  /*@ invariant getTransactions().length <= MAX_TRANSACTIONS ; */

  /** @return What is my JohnnyCard id?*/
  //@ requires true;
  //@ ensures \result == johnnyCardId;
  public final /*@ pure */ int getJohnnyCardId() {
    return johnnyCardId;
  }
  
  /** @param theId Set the johnny card id*/
  //@ requires true;
  //@ assignable johnnyCardId;
  //@ ensures getJohnnyCardId() == theId;
  public final void setJohnnyCardId(final int theId) {
    johnnyCardId = theId;
  }

  /** @return How much cash on this JohnnyCard?*/
  //@ requires true;
  //@ ensures \result == balance;
  public final /*@ pure */ int getBalance() {
    return balance;
  }

  /**@param theBalance Change the amount of cash on this JohnnyCard.*/
  //@ requires theBalance >= 0 && theBalance <= MAX_AMOUNT;
  //@ assignable balance;
  //@ ensures getBalance() == theBalance;
  public final void setBalance(final int theBalance) {
    //@ assert theBalance <= MAX_AMOUNT;
    assert theBalance <= MAX_AMOUNT;
    
    if (theBalance >= 0 && theBalance <= MAX_AMOUNT) {
      balance = theBalance;
    }
  }

  //@ requires true;
  /*@ ensures (\forall int i; 0 <= i && i < transactions.length;
     transactions[i] == \result[i]); */
  /** @return What are the last five transactions. */
  public final /*@ pure */ JohnnyTransaction[] getTransactions() {
    return (JohnnyTransaction[]) transactions.clone();
  }
  
  /** @param theTransactions Set the transactions. */
  //@ requires true;
  //@ assignable transactions;
  /*@ ensures (\forall int i; 0 <= i && i < theTransactions.length;
    getTransactions()[i] == theTransactions[i]); */
  public final void setTransactions(final JohnnyTransaction[] theTransactions) {
     transactions = (JohnnyTransaction[]) theTransactions.clone();
  }

  /**@param theTransaction Add a new JOHNNY_TRANSACTION to this card.*/
  //@ requires true;
  //@ assignable transactions;
  //@ ensures getTransactions().length <= MAX_TRANSACTIONS;
  public final void addTransaction(final JohnnyTransaction theTransaction) {
    if (transactions == null) {
      transactions = new JohnnyTransaction[0];
    }
    
    int startcopy = 0;
    if (transactions.length == MAX_TRANSACTIONS) {
      startcopy = 1;
    }
    
    final JohnnyTransaction[] temp = 
      new JohnnyTransaction[transactions.length + 1 - startcopy];
    
    System.arraycopy(transactions, startcopy, temp, 
                     0, transactions.length - startcopy);
    
    transactions = temp;
  }
  
  /**@param amount Adjust the account balance up and down.*/
  //@ requires balance + amount >= MIN_AMOUNT;
  //@ requires balance + amount <= MAX_AMOUNT;
  //@ ensures getBalance() == \old(balance) + amount;
  //@ assignable balance;
  public final void adjustBalance(final int amount) {
    //@ assert balance + amount >= MIN_AMOUNT;
    assert balance + amount >= MIN_AMOUNT;
    balance += amount;
  }

  /** @return What is the lock state of this JohnnyCard? */
  //@ requires true;
  //@ ensures \result == locked;
  public final /*@ pure */ boolean isLocked() {
    return locked; 
  }

  /** @param theLocked Change the lock state of the JohnnyCard*/
  //@ requires true;
  //@ assignable locked;
  //@ ensures isLocked() == theLocked;
  public final void setLocked(final boolean theLocked) {
    locked = theLocked;
  }

}
