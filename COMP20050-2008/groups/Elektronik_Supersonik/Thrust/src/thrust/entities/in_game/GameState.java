package thrust.entities.in_game;

/**
 * @author Dominic Carr (dominiccarr@gmail.com).
 * @version 11 April 2008
 */

public class GameState extends AbstractGameState {
  
  /**
   * An integer to store the bonus.
   */
  private int my_bonus;
  /**
   * An integer storing the current fuel.
   */
  private int my_current_fuel;
  /**
   * An byte storing lives.
   */
  private byte my_lives; 
  /**
   * An integer storing the maximum fuel.
   */
  private int my_max_fuel;
  /**
   * An integer storing the score.
   */
  private int my_score;

  public void add_high_score(final HighScoreInterface the_new_high_score) {
    // TODO Auto-generated method stub
  }

  public int bonus() {
    return my_bonus;
  }

  public void change_lives(final byte some_new_lives) {
    my_lives += some_new_lives;
  }

  public void change_score(final int some_new_points) {
    my_score += some_new_points;
  }

  public int current_fuel() {
    return my_current_fuel;
  }

  public HighScoreInterface high_score(final int the_index) {
    // TODO Auto-generated method stub
    return null;
  }

  public HighScoreInterface[] high_scores() {
    // TODO Auto-generated method stub
    return null;
  }

  public byte lives() {
    return my_lives;
  }

  public int maximum_fuel() {
    return my_max_fuel;
  }

  public void new_bonus(final int the_new_value) {
    my_bonus = the_new_value;
  }

  public boolean new_high_score(
      final HighScoreInterface the_possible_new_high_score) {
    // TODO Auto-generated method stub
    return false;
  }

  public int score() {
    return my_score;
  }
}