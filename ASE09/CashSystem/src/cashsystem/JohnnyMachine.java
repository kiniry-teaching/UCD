package cashsystem;

/**
 * A terminal for using Johnny Cards. Adds cash to a Johnny Card. Used to manage
 * funds of a Johnny Card.
 *
 * @author Fergus (fergusmccann@yahoo.com)
 * @version 27 April 2009
 */
public class JohnnyMachine {

  /** Maximum number of incorrect PIN attempts allowed before the Johnny Card is locked. */
  private static final int MAX_PIN_ATTEMPTS = 3;

  /** The inserted JohnnyCard. */
  private /*@ spec_public nullable @*/ JohnnyCard johnnyCard;

  /** The JohnnyBank. */
  private final /*@ spec_public @*/ JohnnyBank johnnyBank;
  //@ invariant johnnyBank != null;

  /** The location of the JohnnyMachine. */
  private final /*@ spec_public @*/ String location;
  //@ invariant location != null;

  /** Flag indicating whether or not the inserted JohnnyCard has been PIN validated. */
  private /*@ spec_public @*/ boolean pinValid;

  /** Count of the number of incorrect PIN attempts for the inserted JohnnyCard. */
  private /*@ spec_public @*/ int pinAttempts;

  /*@ invariant pinAttempts >= 0; */

  /**
   * Create a new JohnnyMachine.
   */
  /*@
    requires loc != null;
    requires bank != null;
    ensures
      location == loc &&
      johnnyBank == bank &&
      johnnyCard == null;
   */
  public JohnnyMachine(final String loc, final JohnnyBank bank) {
    this.location = loc;
    this.johnnyBank = bank;
  }

  /**
   * @return How much cash is on the Johnny Card ?
   */
  /*@
     requires johnnyCard != null;
     requires johnnyCard.isLocked() == false;
     requires isPinValid() == true;
   */
  public/*@ pure @*/int getJohnnyCardBalance() {
    return johnnyCard.getBalance();
  }

  /**
   * @return What are the last transactions on this Johnny Card?
   */
  /*@
     requires johnnyCard != null;
     requires johnnyCard.isLocked() == false;
     requires isPinValid() == true;
   */
  public JohnnyTransaction[] getJohnnyCardTransactions() {
    return johnnyCard.getLastTransactions();
  }

  /**
   * @param The Johnny Card
   */
  /*@
     requires card != null;
     ensures this.johnnyCard == card;
     ensures pinValid == false;
     ensures pinAttempts == 0;
   */
  public void insertCard(final /*@ non_null @*/JohnnyCard card) {
    this.johnnyCard = card;
    pinValid = false;
    pinAttempts = 0;
  }

  /**
   */
  /*@
     ensures johnnyCard == null;
     ensures pinValid == false;
     ensures pinAttempts == 0;
   */
  public void removeCard() {
    johnnyCard = null;
    pinValid = false;
    pinAttempts = 0;
  }

  /**
   * @param The PIN
   */
  /*@
     requires cardInserted() == true;
     requires cardIsLocked() == false;
     assignable pinValid;
     assignable pinAttempts;
     assignable johnnyCard.locked;
   */
  public void enterPIN(final int pin) {
    pinValid = (johnnyCard.getPin() == pin);
    if (!pinValid) {
      pinAttempts++;
      if (pinAttempts >= MAX_PIN_ATTEMPTS) {
        johnnyCard.lock();
      }
    }
  }

  /**
   * @return Is the provided PIN valid ?
   */
  /*@ requires cardInserted();
   */
  public/*@ pure @*/boolean isPinValid() {
    return pinValid;
  }

  /**
   * @param Credit the Johnny Card with this amount of cash from bank account
   */
  /*@
     requires cardInserted();
     requires amount > 0;
     requires isPinValid() == true;
     requires getCardBalance() + amount >= 0;
     requires getCardBalance() + amount <= JohnnyCard.MAX_BALANCE;
     requires cardIsLocked() == false;
     requires getCardBankBalance() >= amount;
   */
  public void topupCard(final int amount) {
    johnnyBank.withdraw(johnnyCard.getAccountId(), amount);
    johnnyCard.updateBalance(amount, location, System.currentTimeMillis());
  }

  /**
   * @param Return specified cash amount from Johnny Card to bank account
   */
  /*@
     requires cardInserted();
     requires cardIsLocked() == false;
     requires isPinValid() == true;
     requires amount > 0;
     requires getCardBalance() - amount >= 0;
     requires getCardBalance() - amount <= JohnnyCard.MAX_BALANCE;
   */
  public void lodgeToBank(final int amount) {
    johnnyBank.lodge(johnnyCard.getAccountId(), amount);
    johnnyCard.updateBalance((-amount), location, System.currentTimeMillis());
  }

  /**
   *
   * @return
   */
  /*@
    ensures \result <==> johnnyCard != null;
   */
  public /*@ pure */ boolean cardInserted() {
    return johnnyCard != null;
  }

  /**
  *
  * @return
  */
 /*@
   requires cardInserted();
   ensures \result <==> johnnyCard.isLocked();
  */
  public /*@ pure */ boolean cardIsLocked() {
    return johnnyCard.isLocked();
  }

  /*@
    requires cardInserted();
    requires cardIsLocked() == false;
    ensures \result == johnnyCard.getBalance();
   */
  public /*@ pure */ int getCardBalance() {
    return johnnyCard.getBalance();
  }

  /**
   * @return How much cash do I have in my bank account ?
   */
  /*@
   requires cardInserted();
   requires cardIsLocked() == false;
   ensures \result == johnnyBank.getBankBalance(johnnyCard.getAccountId());
  */
  public /*@ pure */ int getCardBankBalance() {
    return johnnyBank.getBankBalance(johnnyCard.getAccountId());
  }
}
