package cashsystem;

/**
 * A point-of-sale terminal through which one makes Johnny Card transactions.
 *
 * @author Fergus (fergusmccann@yahoo.com)
 * @version 27 April 2009
 */
public class JohnnyRegister {

  /** The maximum number of transactions recorded. */
  public static final int MAX_TRANSACTIONS = 500;

  /** The inserted JohnnyCard. */
  private /*@ spec_public @*/JohnnyCard johnnyCard;

  /** The JohnnyBank. */
  private final /*@ spec_public @*/JohnnyBank johnnyBank;
  //@ invariant johnnyBank != null;

  /** The accountId associated with the JohnnyRegister. */
  private final /*@ spec_public @*/int accountId;
  //@ invariant JohnnyBank.isBankAccountValid(accountId) == true;

  /** The current balance on the JohnnyRegister, that is the total of all transactions since the last bank lodgement. */
  private /*@ spec_public @*/int balance;
  //@ invariant balance >= 0;

  /** The location of the JohnnyRegister. */
  private final /*@ spec_public @*/String location;
  //@ invariant location != null;

  /** The log of transactions on the JohnnyRegister. */
  private /*@ spec_public @*/JohnnyTransaction[] transactions;
  /*@
    invariant
    transactions != null &&
    transactions.length == MAX_TRANSACTIONS;
    invariant \typeof(transactions) == \type(JohnnyTransaction[]);
  */

  /** Indicates last position in array of transactions. */
  private /*@ spec_public @*/ int txIndex;
  /*@ invariant txIndex >= 0 && txIndex < MAX_TRANSACTIONS; */

  /** Number of transactions saved. */
  private /*@ spec_public */ int txCount;
  //@ invariant txCount >=0 && txCount <= MAX_TRANSACTIONS;

  /**
   * Create a new JohnnyRegister.
   */
  /*@
    requires JohnnyBank.isBankAccountValid(account) == true;
    requires loc != null;
    requires bank != null;
    ensures
      accountId == account &&
      location == loc &&
      johnnyBank == bank &&
      transactions.length == MAX_TRANSACTIONS &&
      getBalance() == 0 &&
      johnnyCard == null;
   */
  public JohnnyRegister(final int account, final String loc, final JohnnyBank bank) {
    this.accountId = account;
    this.location = loc;
    this.johnnyBank = bank;
    this.balance = 0;
    this.transactions = new JohnnyTransaction[MAX_TRANSACTIONS];
    this.johnnyCard = null;
  }

  /**
   * @return What is the balance on the Johnny Register?
   */
  /*@
  requires true;
  ensures \result == balance;
  */
  public/*@ pure @*/int getBalance() {
    return balance;
  }

  /**
   * @param Set the balance on the Johnny Register?
   */
  /*@
  requires amount >= 0;
  assignable balance;
  ensures getBalance() == \old(amount);
  */
  public void setBalance(final int amount) {
    balance = amount;
  }

  /**
   * @return What are the transactions on the Register?
   */
  /*@
      invariant true;
      ensures true;
   */
  public JohnnyTransaction[] getTransactions() {
    final JohnnyTransaction [] result = new JohnnyTransaction[transactions.length];
    System.arraycopy(transactions, 0, result, 0, transactions.length);
    return result;
  }

  /**
   * @param The Johnny Card
   */
  /*@
     ensures johnnyCard == card;
   */
  public void insertCard(/*@ non_null @*/final JohnnyCard card) {
    johnnyCard = card;
  }

  /**
   * Remove the Johnny Card.
   */
  /*@
     requires johnnyCard != null;
     assignable johnnyCard;
     ensures johnnyCard == null;
   */
  public void removeCard() {
    johnnyCard = null;
  }

  /**
   * @param Charge the specified amount to the Johnny Card
   */
  /*@
     requires johnnyCard != null;
     requires amount < 0;
     requires johnnyCard.isLocked() == false;
     requires johnnyCard.getBalance() + amount >= 0;
     requires johnnyCard.getBalance() + amount <= JohnnyCard.MAX_BALANCE;
     ensures johnnyCard.getBalance() == \old(johnnyCard.getBalance() - amount);
     ensures getBalance() == \old(getBalance() + amount);
   */
  public void chargeCard(final int amount) {
    final long txTime = System.currentTimeMillis();
    johnnyCard.updateBalance(amount, location, txTime);
    addTransaction(new JohnnyTransaction(amount, location, txTime));
    setBalance(getBalance() + amount);
  }

  /**
   * @param Lodge balance to bank
   */
  /*@
     requires johnnyBank != null;
     ensures johnnyBank.getBankBalance(accountId) == \old(johnnyBank.getBankBalance(accountId) + getBalance());
     ensures getBalance() == 0;
   */
  public void lodgeToBank() {
    johnnyBank.lodge(accountId, getBalance());
    addTransaction(new JohnnyTransaction(getBalance(), location, System.currentTimeMillis()));
    setBalance(0);
  }

  /*@
   ensures \result <==> johnnyCard != null;
  */
  public/*@ pure */boolean cardInserted() {
    return johnnyCard != null;
  }

  /**
   * @return
   */
  /*@
   requires cardInserted();
   ensures \result <==> johnnyCard.isLocked();
  */
  public/*@ pure */boolean cardIsLocked() {
    return johnnyCard.isLocked();
  }

  /*@
    requires cardInserted();
    requires cardIsLocked() == false;
    ensures \result == johnnyCard.getBalance();
  */
  public/*@ pure */int getCardBalance() {
    return johnnyCard.getBalance();
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
