package thrust.entities.about;

/** Extends GameState, calls HighScore class.
 * @author Nicholas McCarthy (nicholas.mccarthy@gmail.com)
 * @version 27 April 2008
 */
public class GameState extends AbstractGameState {

  /** Instance of HighScore class implementing HighScoreInterface. */
  private static HighScore my_highscore;
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

/** Following methods implement HighScore instance. */

  public int high_score(final int the_index) {
    return my_highscore.high_score(the_index);
  }

  public int[] high_scores() {
    return my_highscore.high_scores();
  }

  public void add_high_score(final int the_new_high_score) {
    my_highscore.add_high_score(the_new_high_score);
  }

  public boolean new_high_score(final int the_high_score) {
    return my_highscore.new_high_score(the_high_score);
  }

  public int score() {
    return my_highscore.score();
  }
}
