package johnnycash;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

/**
 * This class contains static utility functions.
 * @author gerard quilty
 */
public final class JohnnyUtil {

  /** private constructor. */
  private JohnnyUtil() {
    
  }
  
  /** @param message Tell the user something. */
  public static void tellUser(final /*@ non_null @*/ String message) {
    System.out.println(message);
  }
  
  /**@param string string to check if integer.
   * @return apparently the most efficient way to 
   * check if a string is an integer in java. */
  public static boolean isIntegerCharacterMatching(final String string) {
    boolean hasSucceeded = true;
    
    for (int i = 0; i < string.length(); i++) {
     final char nextC = string.charAt(i);
     if (!(Character.isDigit(nextC))) {
       hasSucceeded = false;
       break;
     }
    }
    return hasSucceeded;
   }
  
  /** Displays important infomation to the user at the start. */
  public static void welcomeMessage() {
    tellUser("Thank you for joining the Johnny Cash Banking System.");
    tellUser("You're new bank account has been credited with 1000 Euros.");
    tellUser("Please visit a Johnny Cash machine to change the "
             + "default pin on you're new Johnny Cash card.");
    tellUser("The default pin is \"1111\".");
  }
  
  /** Displays the terminal interface screen. */
  public static void terminalMessage() {
    tellUser("You can do any of the following");
    tellUser("  Add cash to your card. (a)");
    tellUser("  Remove cash from your card. (r)");
    tellUser("  Change your PIN. (c)");
    tellUser("  Exit Terminal. (x)");
  }
  
  /** @return Read a user input. */
  public static String readString() {
    String curLine = "";
    final InputStreamReader converter = new InputStreamReader(System.in);
    final BufferedReader input = new BufferedReader(converter);
    try {
      curLine = input.readLine();
    } catch (IOException e) {
      tellUser("Error with input:" + e.getMessage());
    }
    //tellUser(CurLine);
    return curLine;
  }
  
  /** @return Reads a user input that is an integer. */
  public static int readInt() {  
    String input = readString();
    while (!JohnnyUtil.isIntegerCharacterMatching(input)) {
      tellUser("Please input a valid number.");
      input = readString();
    }

    return Integer.parseInt(input);
  }
  
  /** @return Reads a user input that is an character. */
  public static char readChar() {      
    return readString().charAt(0);
  }
}
