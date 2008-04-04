/**
 * @author patrick Nevin: 06754155
 * @created 04/04/08
 */
package thrust.input;

public class DisplayHighScores  extends KeyBoardInput {
  
  
  private static final char DISPLAY_KEY = 'h';
  
  public DisplayHighScores() {
    this.set_key_code();
  }
  
  private void set_key_code( ) {
    super.set_key_code(DISPLAY_KEY);
  }

}
