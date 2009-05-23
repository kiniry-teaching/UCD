package johnnycash;

/** An example ditigal cash system.
 * @author Gerard Quilty
 */
public final class Johnny {
  /** This is the amount defaulted to the bank account.*/
  private static final int DEFAULT_AMOUNT = 1000;
  /** This is the default pin of the johnny card. */
  private static final int DEFAULT_PIN = 1111;
  /** This is the maximum amount allowed to be added to the card. */
  private static final int DAILY_AMOUNT = 250;
  /** This is the maximum amount allowed on the card. */
  private static final int MAX_AMOUNT = 500;
  /** This is the maximum pin. */
  private static final int MAX_PIN = 9999;
  
  /** An instance of a JohnnyBank. */
  private static /*@ spec_public */JohnnyBank bank;
  /** An instance of a JohnnyMachine. */
  private static /*@ spec_public */JohnnyMachine machine;
  /** An instance of a JohnnyRegister. */
  private static /*@ spec_public */JohnnyRegister register;
  /** An instance of a JohnnyCard. */
  private static /*@ spec_public */JohnnyCard card;
  
  /** Private constructor. */
  private Johnny() {
    
  }
  
  /**Runs an interactive loop exercising a demonstration
   * Johnny Card system.
   * @param theArgs the arguments of the program.*/
  public static void main(final /*@ non_null @*/ String[] theArgs) {
    // Initialize the Johnny Card system.
    // Tell the user that they have an empty card.
    // LOOP
    // What does the user want to do with their card?      
    initialize();
    //Tell the user about the system:
    JohnnyUtil.welcomeMessage();
    while (!card.isLocked()) {      
      if (cardInTerminal()) {
        showTerminal();
      } else {
        showRegister();
      }
    }
  }
    /** Initialize the Johnny Card system. */
    //@ requires true;
    //@ assignable bank;
    //@ assignable machine;
    //@ assignable register;
    //@ assignable card;
    //@ ensures bank != null;
    //@ ensures machine != null;
    //@ ensures register != null;
    //@ ensures card != null;
    private static void initialize() {
      bank = new JohnnyBank();
      machine = new JohnnyMachine();
      register = new JohnnyRegister();
      card = new JohnnyCard();
      
      bank.setPin(DEFAULT_PIN);
      bank.setBalance(DEFAULT_AMOUNT);
      bank.initialiseJohnnyCard(card);
      
      machine.setJohnnyBank(bank);
      machine.setJohnnyCard(card);
      register.setJohnnyCard(card);
      register.setItemCost(1);
    }
    
    /** @return What does the user want to do with their card? */
    private static boolean cardInTerminal() {
      // Tell the user that they can either insert their card into a terminal
      // 't' or a register 'r'.
      // Ask the user what they want to do.
      // Return the user's decision.      
      
      JohnnyUtil.tellUser("\n\nYou can insert your card into " 
        + "a terminal(t) or a register(r).");
      JohnnyUtil.tellUser("What do you want to do?");

      String input = JohnnyUtil.readString();
      
      while (!input.equalsIgnoreCase("t") 
          && !input.equalsIgnoreCase("r")) {
        JohnnyUtil.tellUser("Invalid selection.");
        JohnnyUtil.tellUser("\nYou can insert your card into " 
         + "a terminal(t) or a register(r).");
        JohnnyUtil.tellUser("What do you want to do?");

        input = JohnnyUtil.readString();
      }
      
      return input.equalsIgnoreCase("t");
    }

    /** shows the Register interface. */
    private static void showRegister() {
      //   REGISTER:
      //     Does the user accept a sale of value 1?  
      if (card.getBalance() <= register.getItemCost()) {
        JohnnyUtil.tellUser("You do not have enough money in your"
                 + " card to accept a charge of 1 euro.");
        JohnnyUtil.tellUser("Exiting register.");
        return;
      }
      
      JohnnyUtil.tellUser("Do you accept a charge of 1 euro?");
      JohnnyUtil.tellUser("Yes(y) or No(n)");
      if (JohnnyUtil.readString().equalsIgnoreCase("y")) {
        register.requestCost(1);
      }
      JohnnyUtil.tellUser("Exiting register.");
    }

    /** Shows the Terminal interface. */
    private static void showTerminal() {
      //   TERMINAL:
      //     LOOP
      //       Tell the user their balance.
      //       Ask the user if they wish to add or remove cash 
      //       from the card, or pull their card out.
      //       ADD:
      //         Ask the user how much they wish to add.
      //         Add that value to the card (if possible).
      //       REMOVE:
      //         Ask the user how much they wish to remove.
      //         Remove that value to the card (if possible).
      //       PULL:
      //         Tell the user their new balance.
      JohnnyUtil.tellUser("Please enter your pin.");
        machine.validatePin(JohnnyUtil.readInt());
        
        if (!machine.isPinValid()) {
          JohnnyUtil.tellUser("Incorrect PIN. Your card has been locked.");
          JohnnyUtil.tellUser("Exiting system.");
          return;
        }
       
        showBalances();
        JohnnyUtil.terminalMessage();
          
        terminalInput(JohnnyUtil.readChar());
        
        JohnnyUtil.tellUser("Exiting terminal.");
    }

    /** Display the user bank and card balances. */
    private static void showBalances() {
      JohnnyUtil.tellUser("Your bank balance is " 
               + Integer.toString(bank.getBalance()));
      JohnnyUtil.tellUser("Your card balance is " 
               + Integer.toString(card.getBalance()));
    }

    /** Change a users pin. */
    private static void changePin() {
      JohnnyUtil.tellUser("Please enter your new PIN?");
      int input = JohnnyUtil.readInt();
       while (!validateNewPin(input)) {
         JohnnyUtil.tellUser("Please enter your new PIN?");
         input = JohnnyUtil.readInt();
       }
    }

    /** Remove money from a users card. */
    private static void removeMoney() {
      JohnnyUtil.tellUser("How much do you want to remove?");
      
      int valueToTransfer = JohnnyUtil.readInt();
      
      while (removeFunds(valueToTransfer)) {
        JohnnyUtil.tellUser("How much do you want to remove?");
        valueToTransfer = JohnnyUtil.readInt();
      }

      showBalances();
    }

    /** Adds money to a users card. */
    private static void addMoney() {
      JohnnyUtil.tellUser("How much do you want to add?");
      
      int valueToTransfer = JohnnyUtil.readInt();
      
      while (transferFunds(valueToTransfer)) {
        JohnnyUtil.tellUser("How much do you want to add?");
        valueToTransfer = JohnnyUtil.readInt();
      }
 
      showBalances();
    }
 
    /** @param input Takes a users input and 
     *  redirects them to the correct screen. */
    private static void terminalInput(final char input) {
      switch (input) {
        case 'a':
          addMoney();
          break;
        case 'r':
          removeMoney();
          break;
        case 'c':
          changePin();
          break;
        case 'x':
          break;
        default:
          JohnnyUtil.tellUser("Sorry, I don't understand that command.");
      }
    }

    /** @return Try to transfer funds from a bank account to a card. 
     * @param valueToTransfer the amount to add.*/
    private static boolean transferFunds(final int valueToTransfer) {
      //Validate that the value they want to add is correct
      boolean hasNotSucceed = true;
      if (valueToTransfer > machine.getBankBalance()) {
        JohnnyUtil.tellUser("You do not have " + valueToTransfer 
                 + " Euros in your bank account.");
      } else if (valueToTransfer + machine.getCardBalance() > MAX_AMOUNT) {
        JohnnyUtil.tellUser("You are limited to 500 2"
        		+ "Euros on your Johnny Card.");
      } else if (valueToTransfer 
          + machine.getJohnnyBank().getDailyAmount() > DAILY_AMOUNT) {
        JohnnyUtil.tellUser("You are limited to adding 250 " 
                 + "Euros per day to your Johnny Card.");
      } else {
        machine.transferFunds(valueToTransfer);
        hasNotSucceed = false;
      }
      
      return hasNotSucceed;
    }
      
    /** @return removes funds from a card and adds them back to an account 
     * @param valueToTransfer the amount to remove*/
    private static boolean removeFunds(final int valueToTransfer) {
        //Validate that the value they want to remove is correct
        boolean hasNotSucceeded = true;
        if (valueToTransfer > machine.getCardBalance()) {
          JohnnyUtil.tellUser("You do not have " + valueToTransfer 
                   + " Euros on your Johnny card.");
        } else {
          machine.transferFunds(valueToTransfer * -1);
          hasNotSucceeded = false;
        }
      
      return hasNotSucceeded;
    }
      
    /** @param newPin the new pin to use.
     * @return changes the pin for this account to be the passed pin. */
    public static boolean validateNewPin(final int newPin) {
      boolean hasSucceeded = false;
      if (newPin < DEFAULT_PIN || newPin > MAX_PIN) {
        JohnnyUtil.tellUser("Your new pin must be a number between 1000 "
                 + "and 9999 and easy for you to remember");
      } else {
        machine.setPin(newPin);
        hasSucceeded = true;
      }
      return hasSucceeded;
    }
    
  }
