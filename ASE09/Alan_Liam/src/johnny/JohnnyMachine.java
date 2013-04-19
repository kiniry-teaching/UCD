package johnny;

/**
 * A terminal for using Johnny Cards. Adds cash to a Johnny Card.
 * Used for managing funds of a Johnny Card.
 *
 * @author Liam McManus
 * @author Alan Cooke
 */

public class JohnnyMachine {

  /** Reference of the JohnnyCard to be used in the machine. */
  private transient /*@ spec_public @*/ JohnnyCard card;
  /** If the card is accepted by the Johnny Machine.*/
  private transient /*@ spec_public @*/ boolean accepted;
  /**Number of attempts to verify pin for the provided card. */
  private transient /*@ spec_public @*/ int cardAttempts;
  /**List of banks register to this instance of Johnny Machine. */
  private final transient /*@ spec_public @*/ JohnnyBank[] listOfBanks;
  /**Maximum number of attempts to validate pin number. */
  public static final int MAX_ATTEMPTS = 3;

  // invariant listOfBanks != null;

  /*@ requires banks != null;
      ensures (\forall int i; 0 <= i && i < banks.length;
              listOfBanks[i] == banks[i]);
   */
  /**Constructor for the JohnnyMachine.
   * Takes an array of type JohnnyBank which are the supported
   * JohnnyBank instances with this newly instantiated JohnnyMachine.
   * @param banks list of current known banks
   */
  public JohnnyMachine(final JohnnyBank[] banks) {
    this.listOfBanks = new JohnnyBank[banks.length];
    for (int i = 0; i < banks.length; i++) {
      listOfBanks[i] = banks[i];
    }
    this.accepted = false;
  }

  /*@ requires card != null && !card.isLocked() &&
               card.getBank() >= 0 &&
               card.getBank() < listOfBanks.length &&
               listOfBanks[card.getBank()] != null;
      ensures \result == listOfBanks[card.getBank()].getBankBalance();
  */
  /**
   * Get the current balance for the bank associated to the card.
   * @return How much cash do I have in my bank account?
   */
  public final int getCashInBankAccount() {
    return listOfBanks[card.getBank()].getBankBalance();
  }
  /** Get the amount of cash available on the JohnnyCard.
   * @return How much cash do I have on my Johnny Card
   */
  //@ requires card != null && !card.isLocked();
  //@ ensures card.getCash() == \result ;
  public final int getCashOnCard() {
    return this.card.getCash();
  }

  /*@ requires accepted == true &&
               amount > 0 &&
               amount <= JohnnyCard.MAX_BALANCE - card.getCash() &&
               amount <= JohnnyBank.MAX_DAILY
                         - listOfBanks[card.getBank()].getDailyTotal() &&
               amount <= listOfBanks[card.getBank()].getBankBalance() &&
               card != null & !card.isLocked() &&
               card.getBank() >= 0 && card.getBank() < listOfBanks.length &&
               listOfBanks[card.getBank()] != null;
    @ ensures (amount + \old(card.getCash())) == card.getCash() &&
              listOfBanks[card.getBank()].getBankBalance() ==
              (\old(listOfBanks[card.getBank()].getBankBalance()) + amount);
   */
  /** Transfer money from bank to card.
   * @param amount How much cash do I want to put on my Johnny Card?
   */
  public final void ammountOfCashToPutOnCard(final int amount) {
      this.deductBalanceFromBank(amount);
      this.increaseCashOnCard(amount);
  }
  /**
   * Accept the Johnny Card for processing.
   * @param submittedCard The card provided to the machine
   */
  //@ requires submittedCard != null && !submittedCard.isLocked();
  //@ ensures card == submittedCard;
  public final void acceptCard(final JohnnyCard submittedCard) {
    this.card = submittedCard;
  }

  /*@ requires pin !=  null &&
               pin.length == listOfBanks[card.getBank()].pin.length &&
              (\forall int i; 0 <= i && i < pin.length;
                            0 <= pin[i] && pin[i] <= 9) &&
              card != null && !card.isLocked() &&
              card.getBank() >= 0 && card.getBank() < listOfBanks.length &&
              listOfBanks[card.getBank()] != null;
      ensures accepted == true || cardAttempts == \old(cardAttempts)+1;
   */
  /**
   * Check this PIN for this account.
   * @param pin  the pin to be checked against that card pin.
   */
  public final void checkPin(final int[] pin) {
    this.accepted = this.listOfBanks[card.getBank()].verifyPin(pin);
    if (!accepted) {
      this.cardAttempts++;
      if (cardAttempts >= MAX_ATTEMPTS) {
          this.lockCard();
      }
    }
  }

  /*@ requires cardAttempts >= MAX_ATTEMPTS &&
               !card.isLocked() && card != null && !card.isLocked();
      ensures card.isLocked();
   */
  /**
   * Lock the Johnny Card.
   */
  private void lockCard() {
    this.card.lock();
  }

  /*@ requires amount >= 0 &&
               amount <= JohnnyCard.MAX_BALANCE - card.getCash() &&
               card != null && !card.isLocked();
      ensures card.getCash() == \old(card.getCash());
   */
  /**
   * Increase this ammount of cash on this Johnny Card.
   * @param amount  the amount of cash to add/remove from JohnnyCard.
   */
  private void increaseCashOnCard(final int amount) {
    this.card.update(amount);
  }

  /*@ requires amount > 0 &&
               amount <= listOfBanks[card.getBank()].getBankBalance() &&
               card != null & !card.isLocked() &&
               card.getBank() >= 0 && card.getBank() < listOfBanks.length &&
               listOfBanks[card.getBank()] != null;
      ensures listOfBanks[card.getBank()].getBankBalance() ==
              \old(listOfBanks[card.getBank()].getBankBalance()) - amount;
   */
  /**
   * Deduct this amount of cash from this Johnny Bank's account balance.
   * @param amount  the amount to be deducted from the bank balance.
   */
  private void deductBalanceFromBank(final int amount) {
    this.listOfBanks[card.getBank()].updateBankBalance(amount);
  }
  /** Check to see if the card has been accepted by the JohnnyMachine.
   * @return Has the card been JohnnyCard been accepted.
   */
  //@ ensures accepted == \result ;
  public /*@ pure @*/final boolean isAccepted() {
    return this.accepted;
  }
}
