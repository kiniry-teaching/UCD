package cashsystem;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * Main's IO class.
 * @author Damian Chojna (damian.chojna@gmail.com)
 * @version 10 May 2009
 */
public class MainIO {

  /** The main input reader. */
  private static final BufferedReader INPUT = new BufferedReader(new InputStreamReader(System.in));
  /** The main output logger for user. */
  private static/*@ non_null */final Logger OUTPUT = Logger.getAnonymousLogger();

  public String readString() {
    String result = null;
    while (result == null) {
      try {
        result = INPUT.readLine();
        processInputString(result);
      } catch (IOException e) {
        OUTPUT.log(Level.SEVERE, "IO error", e);
        result = null;
      }
    }
    return result;
  }

  private void processInputString(final String value) {
    if (value == null) {
      tellUser("That input was not valid, please try again");
    }
  }

  /*@
    ensures \result > 0;
   */
  public int readPositiveInteger() {
    int result = -1;
    while (result <= 0) {
      result = readInteger();
    }
    return result;
  }

  private int readInteger() {
    int result = -1;
    final String value = readString();
    try {
      result = Integer.parseInt(value);
    } catch (NumberFormatException e) {
      tellUser("That is not a valid integer value");
    }
    return result;
  }

  public String getUserMachineSelection() {
    String result = null;

    while (!isValidMachineSelection(result)) {
      tellUser("[a]dd cash to card, [r]emove cash from card or [p]ull card from machine?");
      result = readString();
    }
    return result;
  }

  private boolean isValidMachineSelection(final String value) {
    boolean result = false;
    if (value == null) {
      result = false;
    } else {
      result = value.matches("[arp]");
    }
    return result;
  }

  public int getUserCardOrTerminalSelection() {

    int option = Main.INVALID_OPTION;
    while (option == Main.INVALID_OPTION) {
      option = getCardOrTerminal();
    }
    return option;
  }

  private int getCardOrTerminal() {
    int result = 0;
    tellUser("Enter card into [t]erminal or [r]egister?");
    final String choice = readString();
    if ("t".equals(choice)) {
      result = Main.USE_TERMINAL_OPTION;
    } else if ("r".equals(choice)) {
      result = Main.USE_REGISTER_OPTION;
    } else {
      result = Main.INVALID_OPTION;
    }
    return result;
  }

  public void tellUser(final String str) {
    OUTPUT.info(str);
  }
}
