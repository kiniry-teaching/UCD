/**
 * @author patrick Nevin: 06754155
 * @created 04/04/08
 */
package thrust.input;

public class StartGame extends KeyBoardInput {
  
  
  private static final char START_KEY = ' ';
  
  public StartGame() {
    this.set_key_code();
  }
  
  private void set_key_code( ) {
    super.set_key_code(START_KEY);
  }

}


