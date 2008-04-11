/**
 * @author patrick Nevin: 06754155
 * @created 04/04/08
 */
package thrust.input;

public class TurnLeft extends KeyBoardInput {
  
  
  private static final char LEFT_KEY = 'a';
  
  public TurnLeft() {
    this.set_key_code();
  }
  
  private void set_key_code( ) {
    super.set_key_code(LEFT_KEY);
  }

}


