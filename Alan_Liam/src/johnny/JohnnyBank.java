package johnny;

import java.util.Random;

/**
 * The bank and account with which one or more Johnny Cards can be associated.
 *
 * @author Liam McManus
 * @author Alan Cooke
 */

public class JohnnyBank {

  /**Maximum amount of euros that can be transfered on JohnnyCard per day.*/
  public static final int MAX_DAILY = 250;
  /** Maximum int checked by ESC/Java2. */
  public static final int MAX_INT = 9999999;
  /**Maximum length of a pin number. */
  public static final int PIN_LENGTH = 4;
  /**List of cards associated with this instance of the JohnnyBank.*/
  private /*@ spec_public @*/transient JohnnyCard[] cards;
  /**Current balance of the bank. */
  private /*@ spec_public @*/ transient int balance;
  /**Pin number associated with bank account, one pin per account. */
  private final transient /*@ spec_public @*/ int[] pin;
  /**Current running total of transactions to cards associated to this bank.*/
  private transient /*@ spec_public @*/ int dailyTotal;
  /**The acocunt number associated to the bank.*/
  private final transient/*@ spec_public @*/ int account;
  /**The bank id associated for this instance of a bank.*/
  private final transient /*@ spec_public @*/ int bank;

  //@ invariant 0 <= dailyTotal && dailyTotal <= 250;
  //@ invariant balance >= 0;
  //@ invariant pin != null;
  //@ invariant cards != null;

  /*@ requires newPin != null && newPin.length == PIN_LENGTH &&
               (\forall int i; 0 <= i && i < newPin.length;
                     0 <= newPin[i] && newPin[i] <= 9);
      ensures balance == 0 && bank == newBank &&
              account > 0 && account <= MAX_INT + 1 &&
              (\forall int i; 0 <= i && i < newPin.length;
              pin[i] == newPin[i]) && cards != null;
   */
  /** Constructor for JohnnyBank.
   * @param newBank  refers to the bank on JohnnyMachine.ListOfBanks
   * @param newPin  the pin that will be used for the card
   */
  public JohnnyBank(final int newBank, final int[] newPin) {
    balance = 0;
    this.bank = newBank;
    this.pin = new int[JohnnyBank.PIN_LENGTH];
    for (int i = 0; i < newPin.length; i++) {
      this.pin[i] = newPin[i];
    }
    this.cards = new JohnnyCard[0];
    final Random generator = new Random();
    account = generator.nextInt(JohnnyBank.MAX_INT) + 1;
  }

  /*@ requires pinEntered != null && pinEntered.length == pin.length;
      ensures \result == (\forall int i; 0 <= i && i < pinEntered.length;
                pinEntered[i] == pin[i]);
  */
  /** Verify the pin associated with the JohnnyBank.
   *  There is one Pin number associated with each JohnnyBank.
   * @param pinEntered  the pin entered by the user
   * @return            Is this pin correct?
   */
  public final /*@ pure @*/ boolean verifyPin(final int[] pinEntered) {
    boolean approved = true;
    for (int i = 0; i < pin.length && approved; i++) {
      if (pin[i] != pinEntered[i]) {
         approved = false;
      }
    }
    return approved;
  }

  /*@ requires cards.length != 0 ;
      ensures (\forall int i; 0 <= i && i < cards.length;
                                 \result[i] == cards[i]);
   */
  /** Get the JohnnyCards associated with the instance of the JohnnyBank.
   * @return What are the cards associated with this account */
  public final /*@ pure @*/ JohnnyCard[] getCards() {
    final JohnnyCard[] temp = new JohnnyCard[this.cards.length];
    for (int i = 0; i < cards.length; i++) {
      temp[i] = cards[i];
    }
    return temp;
  }


  //@ requires true;
  //@ ensures dailyTotal == \result;
  /** Get the current daily total used.
   * @return What is the total of todays transactions with the
   *          Johnny Cards associated with this bank? */
  public final /*@ pure @*/ int getDailyTotal() {
    return dailyTotal;
  }


  //@ requires true;
  //@ ensures balance == \result;
  /** Get the Balance of the JohnnyBank instance.
   * @return How much cash is in this account? */
  public final /*@ pure @*/ int getBankBalance() {
    return balance;
  }


  //@ requires true;
  //@ ensures bank == \result;
  /** Get the ID used to reference the current instance of JohnnyBank.
   * @return What is this bank's ID? */
  public /*@ pure @*/ final int getBank() {
    return this.bank;
  }


  //@ requires true;
  //@ ensures account == \result;
  /** Get the account number associated with the instance of JohnnyBank.
   * @return What is the account number for this JohnnyBank? */
  public /*@ pure @*/ final int getAccountNumber() {
    return this.account;
  }

  //@ requires amount > 0 && amount <= balance;
  //@ ensures balance == (\old(balance) - amount);
  /** Update this Johnny Bank with this amount.
   * @param amount   value to be added/deducted from the bank balance
   *                 (Must be a positive integer).
   */
  public final void updateBankBalance(final int amount) {
    balance -= amount;
  }


  //@ requires bank >= 0;
  //@ ensures cards.length == (\old(cards.length)+1);
  /** Add a Johnny Card to this instance of a JohnnyBank. */
  public final void addCard() {
    JohnnyCard[] newCards = new JohnnyCard[cards.length + 1];
    final JohnnyCard card = new JohnnyCard(bank, cards.length);
    for (int i = 0; i < cards.length; i++) {
      newCards[i] = cards[i];
    }
    newCards[cards.length] = card;
    cards = newCards;
  }

  /*@ requires card != null &&
               card.getUniqueID() >= 0 &&
               card.getUniqueID() < cards.length &&
               cards[card.getUniqueID()].isLocked() &&
               cards[card.getUniqueID()] != null;
      ensures !card.isLocked();
   */
  /** Unlock this Johnny Card.
   * @param card  card to be unlocked.
   */
  public final void unlockCard(final JohnnyCard card) {
      cards[card.getUniqueID()].unlock();
  }

  /** Update running daily total by this amount for this johnny card.
   * @param amount   amount to be added to the dailyTotal balance.
   */
  //@ requires amount > 0  && getDailyTotal() + amount <= MAX_DAILY;
  //@ ensures getDailyTotal() == \old(getDailyTotal()) + amount;
  public final void updateDailyTotal(final int amount) {
    dailyTotal = dailyTotal + amount;
  }

  //@ requires true;
  //@ ensures getDailyTotal() == 0;
  /** Reset the daily total. */
  public final void resetDailyTotal() {
    dailyTotal = 0;
  }
}
