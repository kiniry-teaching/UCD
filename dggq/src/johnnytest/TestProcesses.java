package johnnytest;

import java.util.Calendar;
import java.util.Date;

import johnnycash.JohnnyBank;
import johnnycash.JohnnyRegister;
import johnnycash.JohnnyTransaction;
import junit.framework.TestCase;
/** This class includes test writen to test different processes in the Johnny Cash system. */
public class TestProcesses extends TestCase {

  
  /** This creates transactions on the register and passes them to the bank account. */
  public void testTransferOfTransactions() {
    JohnnyBank B1 = new JohnnyBank();
    
    JohnnyRegister R1 = new JohnnyRegister();
    R1.setTerminalId(1);
    
    final Calendar calender = Calendar.getInstance();
    Date today = calender.getTime();
    for(int i = 0; i < 10; i++)
    {
      JohnnyTransaction J = new JohnnyTransaction();
      J.setJohnnyCardId(i);
      J.setTerminalId(1);
      J.setTransactionAmount(i+100);
      
      J.setTransactionDate(today);
      
      R1.addTransaction(J);
    }
    
    R1.moveTransactions(B1);
      
    assertTrue(R1.getTransactions().length == 0);

    for(int i = 0; i < 10; i++)
    {
      assertTrue(B1.getTransactions()[i].getJohnnyCardId() == i);
      assertTrue(B1.getTransactions()[i].getTerminalId() == 1);
      assertTrue(B1.getTransactions()[i].getTransactionAmount() == i+100);
      assertTrue(B1.getTransactions()[i].getTransactionDate() == today);
    }
    
    
}
  
}
