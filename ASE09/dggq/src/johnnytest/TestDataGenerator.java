package johnnytest;

import java.util.Calendar;
import java.util.Date;

import johnnycash.JohnnyBank;
import johnnycash.JohnnyCard;
import johnnycash.JohnnyMachine;
import johnnycash.JohnnyRegister;
import johnnycash.JohnnyTransaction;

public class TestDataGenerator {

  public static int[] getIntArray()
  {
    return new int[]{-501,-500,-250,249,250,500,501, 100000000};
  }
  
  public static Date[] getDateArray()
  {
    /** the only date that gets entered by the system is the current date. */
    Calendar calendar = Calendar.getInstance();
    Date[] d = new Date[1];
    d[0] = calendar.getTime();
    return d;
  }
  
  public static JohnnyBank getJohnnyBank(int n)
  {
    switch(n)
    {
      case 0:
        return new JohnnyBank();
      case 1:
        JohnnyBank B1 = new JohnnyBank();
        B1.adjustToBalance(20000);
        B1.setPin(9903);
        B1.setTransactions(new JohnnyTransaction[3]);
        return B1;
      default: 
        break;
    }
    throw new java.util.NoSuchElementException();
  }
  
  public static JohnnyCard getJohnnyCard(int n)
  {
    switch(n)
    {
      case 0:
        return new JohnnyCard();
      case 1:
        JohnnyCard J1 = new JohnnyCard();
        J1.setBalance(499);
        J1.setLocked(true);
        J1.setTransactions(new JohnnyTransaction[5]);
      default: 
        break;
    }
    throw new java.util.NoSuchElementException();
  }
  
  public static JohnnyTransaction getJohnnyTransaction(int n)
  { 
    switch(n)
    {
      case 0:
        return new JohnnyTransaction();
      case 1:
        JohnnyTransaction J1 = new JohnnyTransaction();
        J1.setJohnnyCardId(1);
        J1.setTerminalId(1);
        J1.setTransactionAmount(100);
        
        Calendar calender = Calendar.getInstance();
        
        J1.setTransactionDate(calender.getTime());
        
        return J1;
      default: 
        break;
    }
    throw new java.util.NoSuchElementException();
  }

  public static JohnnyMachine getJohnnyMachine(int n)
  {
    switch(n)
    {
      case 0:
        return new JohnnyMachine();
      case 1:
        JohnnyMachine J2 = new JohnnyMachine();
        JohnnyCard C2 = new JohnnyCard();
        C2.setJohnnyCardId(10000);
        
        JohnnyBank B2 = new JohnnyBank();
        B2.setBalance(200000);
        B2.setBankAccountId(10000);
        B2.initialiseJohnnyCard(C2);
        
        J2.setJohnnyBank(B2);
        J2.setJohnnyCard(C2);
        
        return J2;
      default: 
        break;
    }
    throw new java.util.NoSuchElementException();
  }
  
  public static JohnnyRegister getJohnnyRegister(int n)
  {
    switch(n)
    {
      case 0:
        return new JohnnyRegister();
      case 1:
        JohnnyRegister R1 = new JohnnyRegister();
        R1.setItemCost(100);
        return R1;
      case 2:
        JohnnyRegister R2 = new JohnnyRegister();
        R2.setTransactions(new JohnnyTransaction[5]);
        return R2;
      default: 
        break;
    }
    throw new java.util.NoSuchElementException();
  }
  
  public static JohnnyTransaction[] getJohnnyTransactionArray()
  {
        JohnnyTransaction[] t = new JohnnyTransaction[0];
        return t;
  }
  
}
