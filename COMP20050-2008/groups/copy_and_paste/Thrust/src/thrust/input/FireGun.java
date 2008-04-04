/**
 * @author patrick Nevin: 06754155
 * @created 04/04/08
 */
package thrust.input;

public class FireGun extends KeyBoardInput {
  
  
  private static final char Fire_KEY = '\r';
  
  public FireGun() {
    this.set_key_code();
  }
  
  private void set_key_code( ) {
    super.set_key_code(Fire_KEY);
  }

}
