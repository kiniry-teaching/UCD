package johnnycash;

import java.util.Calendar;

/** JOHNNY_REGISTER is a point of sell terminal through which one makes
 * JOHNNY_CARD transactions.
 * @author Home
 */
public class JohnnyRegister {
  /**The cost of the item.*/
  private /*@ spec_public */int itemCost;
  /**The transactions which have occurred since the last sync.*/
  private /*@ spec_public */JohnnyTransaction[] transactions;
  /**The card entered into the register.*/
  private /*@ spec_public */JohnnyCard johnnyCard;
  /**The ID of this terminal.*/
  private /*@ spec_public */int terminalId;

  /** constructor for johnny register. */
  public JohnnyRegister() {
    transactions = new JohnnyTransaction[0];
    johnnyCard = new JohnnyCard();
    terminalId = 0;
  }
  
  /** @return How much money in this JohnnyRegister.*/
  //@ requires true;
  //@ ensures \result == itemCost;
  public final /*@ pure */int getItemCost() {
    return itemCost;
  }
  
  /** @param cost Set the money in this JohnnyRegister.*/
  //@ requires true;
  //@ assignable itemCost;
  //@ ensures getItemCost() == cost;
  public final void setItemCost(final int cost) {
    itemCost = cost;
  }

   //@ requires inItemCost > 0;
   //@ requires getJohnnyCard().getBalance() >= inItemCost;
   //@ assignable itemCost;
   //@ assignable johnnyCard;
   //@ assignable transactions;
   /*@ ensures getJohnnyCard().getBalance() 
     == \old(getJohnnyCard().getBalance() - inItemCost); */
   //@ ensures getTransactions().length == \old(getTransactions().length) + 1;
  /** @param inItemCost Request the cash for the item 
      cost from the JOHNNY_CARD. Pay for an item.
      This scenario is tested by the auto generated code and the preconditions. */
  public final void requestCost(final int inItemCost) {
    
    //@ assert inItemCost > 0;
    assert inItemCost > 0;
    //@ assert getJohnnyCard().getBalance() >= inItemCost;
    assert getJohnnyCard().getBalance() >= inItemCost;
    
    if (inItemCost > 0 && getJohnnyCard().getBalance() >= inItemCost) {
      itemCost = inItemCost;
      
      getJohnnyCard().setBalance(getJohnnyCard().getBalance() - inItemCost);
      
      final JohnnyTransaction transaction = createOwnTransaction(inItemCost);
      
      addTransaction(transaction);
      getJohnnyCard().addTransaction(transaction);
      
    }
  }
  
  //@ requires inItemCost > 0;
  //@ assignable \nothing;
  /*@ ensures getTransactions().length
       == \old(getTransactions().length) + 1;
      ensures getTransactions()[getTransactions().length]
        .getTerminalId() == getTerminalId();
      ensures getTransactions()[getTransactions().length]
        .getJohnnyCardId() == getJohnnyCard().getJohnnyCardId();
      ensures getTransactions()[getTransactions().length]
        .getTransactionAmount() == inItemCost;*/
  /** @return Creates a transaction for the passed value.
   * @param inItemCost The passed value. */
  private JohnnyTransaction createOwnTransaction(final int inItemCost) {
    //@ assert inItemCost > 0;
    assert inItemCost > 0;
    
    final JohnnyTransaction transaction = new JohnnyTransaction();
    transaction.setTerminalId(getTerminalId());
    transaction.setJohnnyCardId(getJohnnyCard().getJohnnyCardId());
    transaction.setTransactionAmount(inItemCost);
    
    final Calendar calender = Calendar.getInstance();
    transaction.setTransactionDate(calender.getTime());
    
    return transaction;
  }

  //@ requires true;
  /*@ ensures (\forall int i; 0 <= i && i < transactions.length;
    transactions[i] == \result[i]); */
  /** @return What are the JOHNNY_TRANSACTIONs against this JohnnyRegister?*/
  public final /*@ pure */ JohnnyTransaction[] getTransactions() {
    return (JohnnyTransaction[]) transactions.clone();
  }
  
  /** @param inTransactions What are the JOHNNY_TRANSACTIONs 
      against this JohnnyRegister?*/
  //@ requires true;
  //@ assignable transactions;
  /*@ ensures (\forall int i; 0 <= i && i < inTransactions.length;
    getTransactions()[i] == inTransactions[i]); */
  public final void setTransactions(final JohnnyTransaction[] inTransactions) {
    transactions = (JohnnyTransaction[]) inTransactions.clone();
  }

  /**@param inTransaction Create new JOHNNY_TRANSACTION on the JOHNNY_CARD. */
  //@ requires inTransaction.getTerminalId() == getTerminalId();
  //@ assignable transactions;
  //@ ensures getTransactions().length == \old(getTransactions().length) + 1;
  //@ ensures getTransactions()[getTransactions().length - 1] == inTransaction;
  public final void addTransaction(final JohnnyTransaction inTransaction) {
    if (transactions == null) {
      transactions = new JohnnyTransaction[0];
    }
    
    JohnnyTransaction[] temp = new JohnnyTransaction[transactions.length + 1];
    
    System.arraycopy(transactions, 0, temp, 0, transactions.length);
    
    temp[transactions.length] = inTransaction;
    
    transactions = temp;
  }

  /** @return What is the inserted JOHNNY_CARD id?*/
   //@ requires true;
   //@ ensures \result == johnnyCard;
  public final /*@ pure */ JohnnyCard getJohnnyCard() {
    return johnnyCard;
  }

  /** @param inJohnnyCard Read inserted JOHNNY_CARD id.*/
  //@ requires true;
  //@ assignable johnnyCard;
  //@ ensures getJohnnyCard() == inJohnnyCard;
  public final void setJohnnyCard(final JohnnyCard inJohnnyCard) {
    johnnyCard = inJohnnyCard;
  }

  /** @return What is this terminal id?*/
   //@ requires true;
   //@ ensures \result == terminalId;
  public final /*@ pure */ int getTerminalId() {
    return terminalId;
  }

  /** @param inTerminalId The ID of the terminal. */
  //@ requires true;
  //@ assignable terminalId;
  //@ ensures getTerminalId() == inTerminalId;
  public final void setTerminalId(final int inTerminalId) {
    terminalId = inTerminalId;
  }

 
  //@ requires johnnyBank != null;
  //@ assignable transactions;
  /*@ ensures johnnyBank.getTransactions().length == 
      \old(johnnyBank.getTransactions().length) 
      + \old(getTransactions().length); */
  //@ ensures (getTransactions().length) == 0;
  /** @param johnnyBank Move JOHNNY_TRANSACTIONs to the JOHNNY_BANK_ACCOUNT.
   * Update JohnnyRegister with takings. 
   * this function is tested by the TestProcess.testTransferOfTransactions test.*/
  public final void moveTransactions(final JohnnyBank johnnyBank) {
    assert transactions != null && johnnyBank != null;
    
      for (int i = 0; i < getTransactions().length; i++) {
        johnnyBank.addTransaction(getTransactions()[i]);
        johnnyBank.adjustToBalance(getTransactions()[i].getTransactionAmount());
      }
      transactions = new JohnnyTransaction[0];
  }

}
