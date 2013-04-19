package cashsystem;


/**
 * The main driver for the Johnny Card system.
 *
 * @author Fergus (fergusmccann@yahoo.com)
 * @version 27 April 2009
 */
public final class Main {

  /** Use Terminal option. */
  public static final int USE_TERMINAL_OPTION = 1;

  /** Use Register option. */
  public static final int USE_REGISTER_OPTION = 2;

  /** Invalid option. */
  public static final int INVALID_OPTION = -1;

  /** Main IO class for all user input / output. */
  private static final MainIO IO = new MainIO();

  /** Default pin for card. */
  private static final int DEFAULT_PIN = 1234;

  /** Default Card account number. */
  private static final int DEMO_CARD_ACC_NUMBER = 1;

  /** Default Register account number. */
  private static final int DEMO_REGISTER_ACC_NUMBER = 2;

  /** The inserted JohnnyCard. */
  private final /*@ spec_public non_null @*/JohnnyCard johnnyCard;

  /** The JohnnyMachine. */
  private final /*@ spec_public non_null @*/JohnnyMachine johnnyMachine;

  /** The JohnnyRegister. */
  private final /*@ spec_public non_null @*/JohnnyRegister johnnyRegister;

  /**
   * Private Main constructor.
   */
  private Main() {
    // Create a new JOHHNY_BANK.
    final JohnnyBank johnnyBank = new JohnnyBank();

    // Create a new JOHNNY_MACHINE.
    johnnyMachine = new JohnnyMachine("Spar", johnnyBank);

    // Create a new JOHHNY_REGISTER.
    johnnyRegister = new JohnnyRegister(DEMO_REGISTER_ACC_NUMBER, "Spar", johnnyBank);

    // Create a new JOHNNY_CARD.
    johnnyCard = new JohnnyCard(DEMO_CARD_ACC_NUMBER, DEFAULT_PIN);
  }

  /** @return What does the user want to do with their card? */
  // ensures \result <==> (* User decided to put their card in the terminal. *);
  public boolean cardInTerminal() {
    boolean result = false;
    final int option = IO.getUserCardOrTerminalSelection();
    if (option == USE_TERMINAL_OPTION) {
      result = true;
    } else {
      result = false;
    }

    return result;
  }

  private void run() {
    // Tell the user that they have an empty card.
    IO.tellUser("You have an empty card");
    while (!johnnyCard.isLocked()) {
      final boolean useTerminal = cardInTerminal();
      if (useTerminal) {
        runTerminal();
      } else {
        processRegister();
      }
    }
  }

  private void runTerminal() {
    // Insert the card into the johnnyMachine
    johnnyMachine.insertCard(johnnyCard);
    enterPin();
    while (johnnyMachine.cardInserted() && !johnnyCard.isLocked()) {
      processTerminal();
    }
  }

  private void processTerminal() {
    if (!johnnyCard.isLocked()) {
      IO.tellUser(Integer.toString(johnnyCard.getBalance()));
      final String selection = IO.getUserMachineSelection();
      performTerminalOperation(selection);
    }
  }

  private void performTerminalOperation(final String selection) {
    if ("a".equals(selection)) {
      addCash();
    }
    if ("r".equals(selection)) {
      removeCash();
    }
    if ("p".equals(selection)) {
      pullCard();
    }
  }

 /**
  * Process the register.
  */
  private void processRegister() {
    johnnyRegister.insertCard(johnnyCard);
    IO.tellUser("Do you accept a sale of 1? (Y == Yes, other key == No)");
    final String answer = IO.readString();
    if ("Y".equals(answer)) {
      processUserRegisterSelection();
    }
  }

  private void processUserRegisterSelection() {
    if (canCharge(-1)) {
      johnnyRegister.chargeCard(-1);
    }
  }
  private void addCash() {
    IO.tellUser("How much do you want to add?");
    final int intValue = IO.readPositiveInteger();
    if (canAddCash(intValue)) {
      johnnyMachine.topupCard(intValue);
    } else {
      IO.tellUser("You cannot perform this operation");
    }
  }

  private void removeCash() {
    IO.tellUser("How much do you want to remove?");
    final int intValue = IO.readPositiveInteger();
    if (canLodgeCash(intValue)) {
      johnnyMachine.lodgeToBank(intValue);
    } else {
      IO.tellUser("You cannot perform this operation");
    }
  }

  private void pullCard() {
    if (!johnnyCard.isLocked()) {
      IO.tellUser(Integer.toString(johnnyCard.getBalance()));
      johnnyMachine.removeCard();
    }
  }

  private void enterPin() {
    while (needToEnterPin()) {
      IO.tellUser("Enter PIN:");
      final int pin = IO.readPositiveInteger();
      johnnyMachine.enterPIN(pin);
    }
  }

  /*@
  requires amount > 0;
  ensures \result <==> johnnyMachine.cardInserted() &&
          !johnnyMachine.cardIsLocked() &&
          johnnyMachine.isPinValid() &&
          (johnnyMachine.getCardBalance() - amount >= 0) &&
          (johnnyMachine.getCardBalance() - amount <= JohnnyCard.MAX_BALANCE);
  */
  private /*@ pure */ boolean canLodgeCash(final int amount) {
    return (johnnyMachine.cardInserted() &&
          !johnnyMachine.cardIsLocked() &&
          johnnyMachine.isPinValid() &&
          (johnnyMachine.getCardBalance() - amount >= 0) &&
          (johnnyMachine.getCardBalance() - amount <= JohnnyCard.MAX_BALANCE));
  }

  /**
   * @param amount
   * @return
   */
  /*@
    requires amount > 0;
    ensures \result <==> johnnyMachine.cardInserted() &&
        johnnyMachine.isPinValid() &&
        !johnnyMachine.cardIsLocked() &&
        (johnnyMachine.getCardBalance() + amount >= 0) &&
        (johnnyMachine.getCardBalance() + amount <= JohnnyCard.MAX_BALANCE) &&
        (johnnyMachine.getCardBankBalance() >= amount);
   */
  private /*@ pure */ boolean canAddCash(final int amount) {
    return (johnnyMachine.cardInserted() &&
        johnnyMachine.isPinValid() &&
        !johnnyMachine.cardIsLocked() &&
        (johnnyMachine.getCardBalance() + amount >= 0) &&
        (johnnyMachine.getCardBalance() + amount <= JohnnyCard.MAX_BALANCE) &&
        (johnnyMachine.getCardBankBalance() >= amount));
  }

  /*@
     ensures \result <==> johnnyRegister.cardInserted() &&
        !johnnyRegister.cardIsLocked() &&
        (johnnyRegister.getCardBalance() + amount >= 0) &&
        (johnnyRegister.getCardBalance() + amount <= JohnnyCard.MAX_BALANCE);
   */
  private /*@ pure */ boolean canCharge(final int amount) {
    return (johnnyRegister.cardInserted() &&
        !johnnyRegister.cardIsLocked() &&
        (johnnyRegister.getCardBalance() + amount >= 0) &&
        (johnnyRegister.getCardBalance() + amount <= JohnnyCard.MAX_BALANCE));
  }

  /*@
    ensures \result <==> johnnyMachine.cardInserted() && !johnnyMachine.cardIsLocked() && !johnnyMachine.isPinValid();
   */
  private /*@ pure */ boolean needToEnterPin() {
    return johnnyMachine.cardInserted() && !johnnyMachine.cardIsLocked() && !johnnyMachine.isPinValid();
  }

  /**
   * Runs an interactive loop exercising a demonstration Johnny Card system.
   *
   * @param the_args
   *        the arguments of the program.
   */
  public static void main(final/*@ non_null @*/String[] the_args) {

    // Initialize the Johnny Card system.
    final Main main = new Main();
    main.run();
  }
}
