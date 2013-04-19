package johnnycash;

import java.util.Calendar;

/** JOHNNY_MACHINE adds CASH to your JOHNNY_CARD and manages a JOHNNY_CARD
 * account.
 * @author Home
 */
public class JohnnyMachine {
  /**The daily limit for transferring money onto the card.*/
  private static final int DAILY_LIMIT = 250;
  /**The maximum amount allowed on the card.*/
  private static final int MAX_AMOUNT = 500;

  /**The bank account associated with the card.*/
  private /*@ spec_public */ JohnnyBank johnnyBank;
  /**The ID of this terminal.*/
  private /*@ spec_public */ int terminalId;
  /**The johnny card in use.*/
  private /*@ spec_public */ JohnnyCard johnnyCard;
  /**Is the PIN entered valid?*/
  private transient /*@ spec_public */boolean pinValid;
  
  /** The constructor for a default johnny machine.*/
  public JohnnyMachine() {
    johnnyBank = new JohnnyBank();
    johnnyCard = new JohnnyCard();
    johnnyBank.initialiseJohnnyCard(johnnyCard);
    pinValid = false;
    terminalId = 1;
  }
  
  /** @return How much cash do I have in my JohnnyBank.*/
  //@ requires true;
  //@ ensures \result == johnnyBank.getBalance();
  public final /*@ pure */ int getBankBalance() {
    return johnnyBank.getBalance();
  }

  /** @return How much cash do I have in my JohnnyCard.*/
  //@ requires true;
  //@ ensures \result == johnnyCard.getBalance();
  public final /*@ pure */ int getCardBalance() {
    return johnnyCard.getBalance();
  }

  /** @return What is the inserted JohnnyCard.*/
  //@ requires true;
  //@ ensures \result == johnnyCard;
  public final /*@ pure */ JohnnyCard getJohnnyCard() {
    return johnnyCard;
  }

  /** @param card Read inserted JohnnyCard id.*/
  //@ requires true;
  //@ assignable johnnyCard;
  //@ ensures getJohnnyCard() == card;
  public final void setJohnnyCard(final JohnnyCard card) {
    johnnyCard = card;
  }

  /** @return What is this terminal id?*/
  //@ requires true;
  //@ ensures \result == terminalId;
  public final/*@ pure */int getTerminalId() {
    return terminalId;
  }

  /** @param theTerminalId the terminal Id. */
  //@ requires true;
  //@ assignable terminalId;
  //@ ensures getTerminalId() == theTerminalId;
  public final void setTerminalId(final int theTerminalId) {
    terminalId = theTerminalId;
  }

  /** Change the JOHNNY_CARD lock state to locked.*/
  //@ requires true;
  //@ assignable johnnyCard;
  //@ ensures johnnyCard.isLocked();
  public final void setLocked() {
    johnnyCard.setLocked(true);
  }

  /** @return Is the entered pin valid?*/
  //@ requires true;
  //@ ensures \result == pinValid;
  public final /*@ pure */ boolean isPinValid() {
    return pinValid;
  }

  /**@param pin Enter the pin. Incorrect PIN use locks card.
   * This scenario is tested by the auto generated code and the post conditions.*/
  //@ requires true;
  //@ assignable johnnyBank;
  //@ assignable pinValid;
  //@ ensures isPinValid() == johnnyBank.isLoggedIn();
  //@ ensures isPinValid() != johnnyCard.isLocked();
  public final void validatePin(final int pin) {
    johnnyBank.isCorrectPin(pin);
    pinValid = johnnyBank.isLoggedIn();
    johnnyCard.setLocked(!pinValid);
  }

  /** @param thePin Change the pin of the JohnnyCard. */
  //@ requires isPinValid();
  //@ assignable johnnyBank;
  //@ ensures thePin == getJohnnyBank().getPin();
  public final void setPin(final int thePin) {
    johnnyBank.setPin(thePin);
  }

  /*@ requires funds > 0; 
    requires funds + getJohnnyBank().getDailyAmount() < DAILY_LIMIT;
    requires getJohnnyBank().getBalance() - funds >= 0;
    requires getJohnnyCard().getBalance() + funds <= MAX_AMOUNT;
    ensures getJohnnyBank().getBalance()
      == \old(getJohnnyBank().getBalance()) - funds;
    ensures getJohnnyCard().getBalance() 
      == \old(getJohnnyCard().getBalance()) + funds;
    */
  /** @param funds cash from JOHNNY_BANK_ACCOUNT to JOHNNY_CARD. 
   * Increase the amount of cash on a card.
    This scenario is tested by the auto generated code and the post conditions.*/
  public final void transferFunds(final int funds) {
    assert funds > 0; 
    assert funds + getJohnnyBank().getDailyAmount() < DAILY_LIMIT;
    assert getJohnnyBank().getBalance() - funds >= 0;
    assert getJohnnyCard().getBalance() + funds <= MAX_AMOUNT;
      
    getJohnnyBank().adjustToBalance(-1 * funds);
    getJohnnyCard().setBalance(getJohnnyCard().getBalance() + funds);
      
    createTransaction(createOwnTransaction(funds));

  }

  
  //@ requires true;
  /*@ ensures getJohnnyBank().getTransactions()
  [getJohnnyBank().getTransactions().length - 1] == theTransaction;*/
  /** @param theTransaction Create new JohnnyTransaction on the Johnnybank.*/
  public final void createTransaction(final JohnnyTransaction theTransaction) {
    getJohnnyBank().addTransaction(theTransaction);
    getJohnnyCard().addTransaction(theTransaction);
  }
  
  /** @return Creates a transaction for the passed value.
   * @param funds The passed value. */
  //@ requires funds > 0 && funds < 500;
  //@ ensures \result.getTerminalId() == getTerminalId();
  //@ ensures \result.getJohnnyCardId() == getJohnnyCard().getJohnnyCardId();
  //@ ensures \result.getTransactionAmount() == funds;
  public final JohnnyTransaction createOwnTransaction(final int funds) {
    //@assert funds > 0;
    assert funds > 0;
    
    final JohnnyTransaction transaction = new JohnnyTransaction();
    transaction.setTerminalId(getTerminalId());
    transaction.setJohnnyCardId(getJohnnyCard().getJohnnyCardId());
    transaction.setTransactionAmount(funds);
    
    final Calendar calender = Calendar.getInstance();
    transaction.setTransactionDate(calender.getTime());
    
    return transaction;
  }

  /** @return Johnny Back account.*/
  //@ requires true;
  //@ ensures \result == johnnyBank;
  public final /*@ pure */ JohnnyBank getJohnnyBank() {
    return johnnyBank;
  }
  
  /** @param theJohnnyBank Set the Bank account details. */
  //@ requires true;
  //@ assignable johnnyBank;
  //@ ensures getJohnnyBank() == theJohnnyBank;
  public final void setJohnnyBank(final JohnnyBank theJohnnyBank) {
    johnnyBank = theJohnnyBank;
  }
  

}
