/**
 * @author patrick Nevin: 06754155
 * @created 04/04/08
 */
package thrust.input;

public class StopGame extends KeyBoardInput {
  
  
  private static final char STOP_KEY = 27;
  
  public StopGame() {
    this.set_key_code();
  }
  
  private void set_key_code( ) {
    super.set_key_code(STOP_KEY);
  }

}
