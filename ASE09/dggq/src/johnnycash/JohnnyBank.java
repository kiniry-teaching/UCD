package johnnycash;

import java.text.SimpleDateFormat;
import java.util.Calendar;
import java.util.Locale;

/** A bank account and a bank.
 * @author Darragh Grogan & Ger Quilty
 * @version 0.0.1
 */
public class JohnnyBank {

  /** Amount must be greater than 0. **/
  private static final int MIN_AMOUNT = 0;
  /** pin must be greater or equal to this number. */
  private static final int BASE_PIN = 1000;
  /** pin must be less than this number. */
  private static final int MAX_PIN = 9999;
  /** The bank account id. */
  private /*@ spec_public */int bankAccountId;
  
  /** The bank balance. */
  private /*@ spec_public */int balance;
  //@ invariant balance >= MIN_AMOUNT;
  
  /** The transactions against this transactions. */
  private /*@ spec_public non_null */JohnnyTransaction[] transactions 
    = new JohnnyTransaction[0];
  //@ invariant transactions != null;
  
  /** The pin number of this bank account. */
  private /*@ spec_public */int pin;
  //@ invariant pin >= 1000 & pin <= 9999;
  
  /** The Id of the johnny card connected to this account. */
  private /*@ spec_public */int johnnyCardId;
  
  /** If someone is logged in correctly to this account. */
  private transient /*@ spec_public */boolean loggedIn;

  /** constructor for Johnny bank. */
  public JohnnyBank() {
    bankAccountId = 1;
    transactions = new JohnnyTransaction[0];
    balance = 0;
    loggedIn = false;
    pin = BASE_PIN;
  }
  
  /** @return What is my JohnnyCard id?*/
  //@ requires true;
  //@ ensures \result == johnnyCardId;
  public final /*@ pure */int getJohnnyCardId() {
    return johnnyCardId;
  }

  /** @param theJohnnyCard Set the JohnnyCard id. 
     Initializes a new card so that it is associated 
     with a specific bank account, contains no cash, is 
     unlocked, and has no transactions in its log.*/
  //@ requires true;
  //@ ensures getJohnnyCardId() == theJohnnyCard.getJohnnyCardId();
  public final void initialiseJohnnyCard(final JohnnyCard theJohnnyCard) {
    johnnyCardId = theJohnnyCard.getJohnnyCardId();
    theJohnnyCard.setBalance(0);
    theJohnnyCard.setLocked(false);
    theJohnnyCard.setTransactions(new JohnnyTransaction[0]);
  }

  /** @param theJohnnyCardId Set the JohnnyCard id. */
  //@ requires true;
  //@ ensures getJohnnyCardId() == theJohnnyCardId;
  public final void setJohnnyCardId(final int theJohnnyCardId) {
    johnnyCardId = theJohnnyCardId;
  }
  
  /** @return What is the bank account ID */
  //@ requires true;
  //@ ensures \result == bankAccountId;
  public final /*@ pure */ int getBankAccountId() {
    return bankAccountId;
  }

  /** @param theBankAccountId Set the bank account ID.*/
  //@ requires bankAccountId > 0;
  //@ ensures getBankAccountId() == theBankAccountId;
  //@ assignable bankAccountId;
  public final void setBankAccountId(final int theBankAccountId) {
    bankAccountId = theBankAccountId;
  }

  /** @return How much cash do I have in my JohnnyBank? */
  //@ requires true;
  //@ ensures \result == balance;
  public final /*@ pure */ int getBalance() {
    return balance;
  }
  
  /** @param theBalance set the amount of cash in my JohnnyBank? */
  //@ requires theBalance >= 0;
  //@ ensures getBalance() == theBalance;
  public final void setBalance(final int theBalance) {
    if (theBalance >= 0) {
      balance = theBalance;
    }
  }

  /**@param amount Adjust the account balance up and down.*/
  //@ requires balance + amount >= MIN_AMOUNT;
  //@ ensures getBalance() == \old(balance) + amount;
  //@ assignable balance;
  public final void adjustToBalance(final int amount) {
    //@ assert balance + amount >= MIN_AMOUNT;
    assert balance + amount >= MIN_AMOUNT;
    balance += amount;
  }

  //@ requires true;
  /*@ ensures (\forall int i; 0 <= i && i < transactions.length;
    transactions[i] == \result[i]); */
  /** @return What are the JohnnyTransaction against this JohnnyBank?*/
  public final /*@ pure */JohnnyTransaction[] getTransactions() {
    return (JohnnyTransaction[]) transactions.clone();
  }

  //@ requires true;
  /*@ ensures (\forall int i; 0 <= i && i < theTransactions.length;
    getTransactions()[i] == theTransactions[i]); */
  /** @param theTransactions What are the JohnnyTransaction against 
   * this JohnnyBank?*/
  public final void setTransactions(final JohnnyTransaction[] theTransactions) {
    transactions = (JohnnyTransaction[]) theTransactions.clone();
  }
  
  /** @param theTransaction add a transaction to this the account
   */
  //@ requires theTransaction != null;
  //@ requires getTransactions() != null;
  //@ requires theTransaction.getTransactionAmount() <= 500;
  //@ requires theTransaction.getTransactionAmount() > 0;
  //@ requires theTransaction.getTransactionDate() != null;
  //@ ensures theTransaction == transactions[transactions.length - 1];
  //@ ensures transactions.length == \old(transactions.length + 1);
  public final void addTransaction(final JohnnyTransaction theTransaction) {

    JohnnyTransaction[] temp = new JohnnyTransaction[transactions.length + 1];
    
    System.arraycopy(transactions, 0, temp, 0, transactions.length);
    
    temp[transactions.length] = theTransaction;
    
    transactions = temp;
  }

  /** @return What are the transaction for this account*/
  //@ requires true;
  //@ ensures \result >= 0;
  public final /*@ pure */int getTransactionCount() {
    return transactions.length;
  }

  /** @param thePin Does the PIN match? */
  //@ requires true;
  //@ ensures loggedIn == (pin == thePin);
  //@ assignable loggedIn;
  public final void isCorrectPin(final int thePin) {
    loggedIn = (thePin == pin);
  }

  /** @return Return Logged in state? */
  //@ requires true;
  //@ ensures \result == loggedIn;
  public final /*@ pure */boolean isLoggedIn() {
    return loggedIn;
  }
  
  /** @param thePin Change the pin.*/
  //@ requires thePin >= BASE_PIN & thePin <= MAX_PIN;
  //@ ensures pin == thePin;
  //@ assignable pin;
  public final void setPin(final int thePin) {
    //@ assert thePin >= BASE_PIN & thePin <= MAX_PIN;
    assert thePin >= BASE_PIN & thePin <= MAX_PIN;
    pin = thePin;
  }
  
  /** @return Return the pin? */
  //@ requires true;
  //@ ensures \result == pin;
  public final /*@ pure */int getPin() {
    return pin;
  }

  /** @return Get the daily amount against this account?*/
  //@ requires transactions != null;
  public final /*@ pure */ int getDailyAmount() {
    assert transactions != null;
    int amount = 0;
      
      final Calendar calender = Calendar.getInstance();
      final SimpleDateFormat dateFormat = 
         new SimpleDateFormat("dd/MM/yyyy", Locale.ENGLISH);
      
      final String todayDate = dateFormat.format(calender.getTime());
      
      for (int i = 0; i < transactions.length; i++) {
        final String transactionDate 
          = dateFormat.format(transactions[i].getTransactionDate());
        
        if (todayDate.compareTo(transactionDate) == 0) {
          amount += transactions[i].getTransactionAmount();
        }
      }
    return amount;
  }

}
