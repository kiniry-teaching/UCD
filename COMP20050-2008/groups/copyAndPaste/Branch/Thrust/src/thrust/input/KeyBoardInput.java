package thrust.input;
/**
 * @author Patrick Nevin (patrick.nevin@ucdconnect.ie)
 * @version 20 April 2008
 */
public class KeyBoardInput {
  /**
   * @requires (int)key_code >= 0 && (int)key_code <= 255
     * ensures true;
     */
  /**
   * @ invariant Key codes are set exactly once per keyboard input.
   */
  private char my_key_code;
  /**
   * @return  What is your key code?
   */
  public char key_code() {
    return this.my_key_code;
  }
  /**
   * @param key
   * @return This character "key", is your key  code
   */

  public void set_key_code(final char a_key) {
    this.my_key_code = a_key;
  }
}


