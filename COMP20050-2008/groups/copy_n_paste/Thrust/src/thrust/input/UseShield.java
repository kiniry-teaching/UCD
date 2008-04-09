/**
 * @author patrick Nevin: 06754155
 * @created 04/04/08
 */
package thrust.input;

public class UseShield extends KeyBoardInput {
  
  
  private static final char SHIELD_KEY = ' ';
  
  public UseShield() {
    this.set_key_code();
  }
  
  private void set_key_code( ) {
    super.set_key_code(SHIELD_KEY);
  }

}


