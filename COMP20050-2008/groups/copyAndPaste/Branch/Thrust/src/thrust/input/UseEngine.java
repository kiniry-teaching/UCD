/**
 * @author patrick Nevin: 06754155
 * @created 04/04/08
 */
package thrust.input;

public class UseEngine extends KeyBoardInput {
  
  
  private static final char ENGINE_KEY = 16;
  
  public UseEngine() {
    this.set_key_code();
  }
  
  private void set_key_code( ) {
    super.set_key_code(ENGINE_KEY);
  }

}


