package johnny;

/**
 * A point-of-sale terminal through which one makes Johnny Card transactions.
 *
 * @author Liam McManus
 * @author Alan Cooke
 *
 */
public class JohnnyRegister {

  /**Submitted card for completing transactions. */
  private transient /*@ spec_public @*/ JohnnyCard card;
  /**Current balance of cash on the card. */
  private transient /*@ spec_public @*/ int balance;

  /** Constructor for JohnnyRegister. */
  //@ ensures balance == 0;
  public JohnnyRegister() {
    balance = 0;
  }

  /** Accept the Johnny Card for processing.
   *
   * @param submittedCard  card provided to the machine
   */
  //@ requires submittedCard != null && !submittedCard.isLocked();
  //@ ensures card != null ;
  public final void acceptCard(final JohnnyCard submittedCard) {
    card = submittedCard;
  }

  /*@ requires balance >= 0 && amount >= 0 && amount <= card.getCash() &&
      card != null && !card.isLocked();
      ensures card.getCash() == \old(card.getCash()) - amount &&
      balance == \old(balance) + amount;
   */
  /** Transfer cash from Johnny Card to Johnny register.
   * @param amount  amount to be added to the card and removed from account.
   */
  public final void transferCash(final int amount) {
    balance += amount;
    card.update(-amount);
  }
}
