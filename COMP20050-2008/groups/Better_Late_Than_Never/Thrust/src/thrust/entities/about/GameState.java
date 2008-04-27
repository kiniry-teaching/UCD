package thrust.entities.about;
/** Extends GameState, calls HighScore class.
 * @author Nicholas McCarthy (nicholas.mccarthy@gmail.com)
 * @version 27 April 2008
 */
public class GameState extends AbstractGameState {

  /** Int holding maximum amount of fuel allowed. */
  private static final int MAX_FUEL = 100000;
  /** HighScore class to keep track of score. */
  private static int my_bonus;
  /** Int to hold current fuel. */
  private static int my_fuel;
  /** Byte to hold current lives. */
  private static byte my_lives;


  public int bonus() {
    return my_bonus;
  }
  public int current_fuel() {
    return my_fuel;
  }

  public int maximum_fuel() {
    return MAX_FUEL;
  }
  public byte lives() {
    return my_lives;
  }

  public void new_bonus(final int the_new_value) {
    my_bonus = the_new_value;
    // TODO Auto-generated method stub

  }

  public void change_lives(final byte some_new_lives) {
    my_lives += some_new_lives;
  }

/**

  public HighScoreInterface high_score(int the_index) {
    // TODO Auto-generated method stub
    return null;
  }

  public HighScoreInterface[] high_scores() {
    // TODO Auto-generated method stub
    return null;
  }




  public void add_high_score(final HighScoreInterface the_new_high_score) {
    // TODO Auto-generated method stub

  }

  public boolean new_high_score(HighScoreInterface the_high_score) {
    // TODO Auto-generated method stub
    return false;
  }

  public int score() {
    // TODO Auto-generated method stub
    return 0;
  }
*/
}
