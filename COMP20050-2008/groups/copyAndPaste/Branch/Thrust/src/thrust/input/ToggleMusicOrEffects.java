/**
 * @author patrick Nevin: 06754155
 * @created 04/04/08
 */
package thrust.input;

public class ToggleMusicOrEffects extends KeyBoardInput {
  
  
  private static final char TOGGLE_KEY = 'm';
  
  public ToggleMusicOrEffects() {
    this.set_key_code();
  }
  
  private void set_key_code( ) {
    super.set_key_code(TOGGLE_KEY);
  }

}
