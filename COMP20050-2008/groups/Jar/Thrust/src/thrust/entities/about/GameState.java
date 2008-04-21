/**
 *
 */
package thrust.entities.about;

/**
 * @author Jar (timbyr@gmail.com)
 * @version 15 April 2008
 */
public class GameState extends AbstractGameState {

  private int current_high_score;
  /*
   * @see thrust.entities.about.AbstractGameState#
   *  add_high_score(thrust.entities.about.AbstractGameState.HighScoreInterface)
   */
  public void add_high_score(final HighScoreInterface the_new_high_score) {
    
  }

  /*
   * @see thrust.entities.about.AbstractGameState#bonus()
   */
  public int bonus() {
    return 0;
  }

  /*
   * @see thrust.entities.about.AbstractGameState#change_lives(byte)
   */
  public void change_lives(final byte some_new_lives) {

  }

  /*
   * @see thrust.entities.about.AbstractGameState#change_score(int)
   */
  public void change_score(final int some_new_points) {

  }

  /*
   * @see thrust.entities.about.AbstractGameState#current_fuel()
   */
  public int current_fuel() {

    return 0;
  }

  /*
   * @see thrust.entities.about.AbstractGameState#high_score(int)
   */
  public HighScoreInterface high_score(final int the_index) {

    return null;
  }

  /*
   * @see thrust.entities.about.AbstractGameState#high_scores()
   */
  public HighScoreInterface[] high_scores() {

    return new HighScoreInterface[0];
  }

  /*
   * @see thrust.entities.about.AbstractGameState#lives()
   */
  public byte lives() {

    return 0;
  }

  /*
   * @see thrust.entities.about.AbstractGameState#maximum_fuel()
   */
  public int maximum_fuel() {

    return 0;
  }

  /*
   * @see thrust.entities.about.AbstractGameState#new_bonus(int)
   */
  public void new_bonus(final int the_new_value) {

  }

  /*
   * @see thrust.entities.about.AbstractGameState#new_high_score(thrust.entities.about.AbstractGameState.HighScoreInterface)
   */
  public boolean new_high_score(final HighScoreInterface the_high_score) {

    return false;
  }

  /*
   * @see thrust.entities.about.AbstractGameState#score()
   */
  public int score() {

    return 0;
  }

}
