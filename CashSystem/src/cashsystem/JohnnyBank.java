package cashsystem;

/**
 * A high street bank providing JOHNNY CASH services to both Johnny Machines and Johnny Registers.
 *
 * @author Fergus (fergusmccann@yahoo.com)
 * @version 27 April 2009
 */
public final class JohnnyBank {

  /** Maximum number of bank accounts. */
  public static final int MAX_ACCOUNTS = 5000;

  /** Initial balance on all accounts. */
  public static final int INITIAL_BALANCE = 500;

  /** Bank accounts.  */
  private /*@ spec_public non_null */ int [] accounts = new int[MAX_ACCOUNTS];
  /*@ invariant accounts.length == MAX_ACCOUNTS; */

  /**
   * Creates a new JohnnyBank. Initializes all accounts with 500.
   */
  public JohnnyBank() {
    for (int i = 0; i < accounts.length; i++) {
      accounts[i] = INITIAL_BALANCE;
    }
  }

  /**
   * @return How much cash is in the account?
   */
  /*@
    requires acct_id > 0 && acct_id < MAX_ACCOUNTS;
    ensures \result == accounts[acct_id];
   */
  public /*@ pure @*/ int getBankBalance(final int acct_id) {
    return accounts[acct_id];
  }

  /**
   * @param The amount of cash to withdraw
   */
  /*@
     requires amount > 0;
     requires acct_id >= 0;
     requires isBankAccountValid(acct_id) == true;
     requires accounts[acct_id] >= amount;

     assignable accounts[*];

     ensures accounts[acct_id] == \old(accounts[acct_id]) - amount;
   */
  public void withdraw(final int acct_id, final int amount) {
    accounts[acct_id] -= amount;
  }

  /**
   * @param The amount of cash to lodge
   */
  /*@
     requires amount >= 0;
     requires acct_id >= 0;

     requires isBankAccountValid(acct_id);

     assignable accounts[*];
     ensures accounts[acct_id] == \old(accounts[acct_id]) + amount;
   */
  public void lodge(final int acct_id, final int amount) {
    accounts[acct_id] += amount;
  }

  /**
   *  .
   * @param number
   * @return
   */
  /*@
    requires true;
    ensures \result <==> (number > 0 && number < JohnnyBank.MAX_ACCOUNTS);
   */
  public static /*@ pure */ boolean isBankAccountValid(final int number) {
    return (number > 0 && number < JohnnyBank.MAX_ACCOUNTS);
  }
}
