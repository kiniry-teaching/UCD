package cashsystem;

/**
 * An industry-standard SmartCard.
 *
 * @author Damian Chojna (damian.chojna@gmail.com)
 * @version 27 April 2009
 */
public class JohnnyCard {

  /** The maximum balance on this card. */
  public static final int MAX_BALANCE = 500;

  /** The maximum number of transactions recorded. */
  public static final int MAX_TRANSACTIONS = 5;

  /** The value on the card in cents. */
  private /*@ spec_public */ int cardValue;
  //@ invariant (cardValue >= 0) && (cardValue <= 500);

  /** Indicates if the card is locked. */
  private /*@ spec_public */ boolean locked;

  /** Keeps the number of transactions performed on the card. */
  private /*@ spec_public non_null */ JohnnyTransaction[] transactions;
  /*@
    invariant
    transactions != null &&
    transactions.length == MAX_TRANSACTIONS;
    invariant \typeof(transactions) == \type(JohnnyTransaction[]);
   */

  /** Indicates last position in array of transactions. */
  private /*@ spec_public */ int txIndex;
  /*@
    invariant txIndex >= 0 && txIndex < MAX_TRANSACTIONS;
   */

  /** Number of transactions saved. */
  private /*@ spec_public */ int txCount;
  /*@
    invariant txCount >=0 && txCount <= MAX_TRANSACTIONS;
   */

  /** The ID of the bank and account that this card belongs to. */
  private final /*@ spec_public */ int accountId;
  //@ invariant JohnnyBank.isBankAccountValid(accountId) == true;

  /** The pin required to access this card. */
  private final /*@ spec_public */int pin;

  /**
   * Create a new JohnnyCard.
   */
  /*@
    requires bank_number > 0 && bank_number < JohnnyBank.MAX_ACCOUNTS;
    ensures
      locked == false &&
      accountId == bank_number &&
      pin == new_pin &&
      cardValue == 0;
   */
  public JohnnyCard(final int bank_number, final int new_pin) {
    this.accountId = bank_number;
    this.pin = new_pin;
    this.locked = false;
    this.cardValue = 0;
    this.txIndex = 0;
    this.txCount = 0;
    this.transactions = new JohnnyTransaction[MAX_TRANSACTIONS];
  }

  /**
   * @return How much cash is on this card?
   */
  /*@
     requires isLocked() == false;
     ensures \result == cardValue;
   */
  public /*@ pure */ int getBalance() {
    return cardValue;
  }

  /**
   * @return What are the last 5 transactions that this card was involved in?
   */
  /*@
     requires isLocked() == false;
     ensures \result.length == txCount;
   */
  public JohnnyTransaction[] getLastTransactions() {

    final JohnnyTransaction[] result = new JohnnyTransaction[txCount];
    int index = (txCount == 0) ? 0 : txCount - 1;
    for (int i = 0; i < txCount; i++) {
      result[i] = transactions[index];
      if (index == 0) {
        index = transactions.length - 1;
      } else {
        index--;
      }
    }
    return result;
  }

  /**
   * @return Is this Johnny Card locked?
   */
  /*@
     requires true;
     ensures \result == locked;
   */
  public /*@ pure */ boolean isLocked() {
    return locked;
  }

  /**
   * @return How much cash am I allowed to credit this card?
   */
  /*@
     requires isLocked() == false;
     ensures \result == MAX_BALANCE - getBalance();
   */
  public /*@ pure */ int getMaxCredit() {
    return (MAX_BALANCE - cardValue);
  }

  /**
   * @return What is the pin?
   */
  /*@
     requires isLocked() == false;
     ensures \result == pin;
   */
  public /*@ pure */ int getPin() {
    return pin;
  }

  /**
   * @return What account does this card belong to?
   */
  /*@
     requires isLocked() == false;
     ensures \result == accountId;
     ensures \result > 0 && \result < JohnnyBank.MAX_ACCOUNTS;
   */
  public /*@ pure */ int getAccountId() {
    return accountId;
  }

  /**
   * Change the amount of cash on this card by this much.
   *
   * @param amount
   * @param locationID
   *          - physical location name
   */
  /*@
     requires (cardValue + amount) >= 0 && (cardValue + amount) <= JohnnyCard.MAX_BALANCE;
     requires isLocked() == false;
     requires location != null;

     ensures getBalance() == \old(cardValue) + amount;
     ensures
       transactions.length > 0 &&
       transactions[txIndex].getAmount() == amount &&
       transactions[txIndex].getLocation() == location &&
       transactions[txIndex].getTimestamp() == timestamp;
   */
  public void updateBalance(final int amount, /*@ non_null */
                            final String location, final long timestamp) {
    final JohnnyTransaction transaction = new JohnnyTransaction(amount, location, timestamp);
    addTransaction(transaction);

    cardValue += amount;
  }

  /**
   * Lock this card
   */
  /*@
     ensures isLocked() == true;
     assignable this.locked;
   */
  public void lock() {
    this.locked = true;
  }

  /**
   * Unlock this card
   */
  /*@
     requires true;
     ensures isLocked() == false;
   */
  public void unlock() {
    locked = false;
  }

  /**
   * Add a transaction to the transactions array.
   * @param newTransaction the new transaction
   */
  /*@
    requires transaction != null;
    ensures transactions[txIndex] == transaction;
   */
  private void addTransaction(final /*@ non_null */ JohnnyTransaction transaction) {
    if (txIndex == MAX_TRANSACTIONS - 1) {
      txIndex = 0;
    } else {
      txIndex++;
    }
    if (txCount < MAX_TRANSACTIONS) {
      txCount++;
    }
    transactions[txIndex] = transaction;
  }
}
