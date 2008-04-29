package thrust.entities.about;
/**
 * @author Ben Fitzgerald (ben.fitz@hotmail.com)
 * @version 28 April 2008
 * */
public class GameState extends AbstractGameState {

  /** An array of the highscores.*/
  private HighScoreInterface[] my_highScores;
  /**The amount of lives a player has.*/
  private byte my_lives;
  /**The bonus score.*/
  private int my_bonus;
  /**The players score.*/
  private int my_score;
  /**The amount of fuel.*/
  private int my_fuel;

  /**
   * @return The bonus
   * */
  public int bonus() {
    return my_bonus;
  }
  /**
   * @param Sets the lives by the amount the lives change by.
   * */
  public void change_lives(final byte some_new_lives) {
    my_lives += some_new_lives;
  }
  /**
   * @param  Sets the score by the amount of new points.
   * */
  public void change_score(final int some_new_points) {
    my_score += some_new_points;
  }
  /**
   * @return The current fuel amount.
   * */
  public int current_fuel() {
    return my_fuel;
  }
  /**
   * @return Highscore Type at a given index.
   * */
  public HighScoreInterface high_score(final int the_index) {
    return my_highScores[the_index];
  }
  /**
   * @return The array of high-scores.
   * */
  public HighScoreInterface[] high_scores() {
    return my_highScores;
  }
  /**
   * @param Adds a score to the high-scores.
   * */
  public void add_high_score(final HighScoreInterface the_new_high_score) {
    // TODO add_high_score method stub
  }
  /**
   * @return The number of lives a player has.
   * */
  public byte lives() {
    return my_lives;
  }
  /**
   * @return The maximum amount of fuel
   * */
  public int maximum_fuel() {
    final int maximum_fuel = 10000;
    return maximum_fuel;
  }
  /**
   * @param Sets the bonus's new value.
   * */
  public void new_bonus(final int the_new_value) {
    my_bonus = the_new_value;
  }
  /**
   * @return A boolean that checks if my_score is a highscore.
   * */
  public boolean new_high_score(final HighScoreInterface the_high_score) {
    for (int x = 0; x < my_highScores.length; x++)
    {
      if (my_score > my_highScores[x].score())
      {
        return true;
      }
    }
    return false;
  }
  /**
   * @return The players score.
   * */
  public int score() {
    return my_score;
  }

}
