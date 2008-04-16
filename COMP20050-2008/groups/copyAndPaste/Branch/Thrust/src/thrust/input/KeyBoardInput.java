/**
 * @author  patrick Nevin: 06754155
 * @created 02/04/08 version 0.1
 */
package thrust.input;

public class KeyBoardInput {   
  /**
   * @requires (int)key_code >= 0 && (int)key_code <= 255
     * ensures true;
     */
  /**
   * @ invariant Key codes are set exactly once per keyboard input.
   */
  
  private char key_code;
  
 
  /**
   * @return  What is your key code?
   */ 
  public char key_code() {
    return this.key_code;
  }
  /**
   * @param key
   * @return This character "key", is your key  code
   */

  public void set_key_code(char key) {
    this.key_code = key;
  }
}


