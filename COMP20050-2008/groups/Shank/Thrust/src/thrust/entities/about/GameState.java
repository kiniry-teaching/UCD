package thrust.entities.about;
/**
 * @author Ben Fitzgerald (ben.fitz@hotmail.com)
 * @version 28 April 2008
 * */
public class GameState extends AbstractGameState {

  public void add_high_score(final HighScoreInterface the_new_high_score) {
    // TODO add_high_score method stub
  }

  public int bonus() {
    // TODO bonus method stub
    return 0;
  }

  public void change_lives(final byte some_new_lives) {
    // TODO change_lives method stub
  }

  public void change_score(final int some_new_points) {
    // TODO change_score method stub
  }

  public int current_fuel() {
    // TODO current_fuel method stub
    return 0;
  }

  public HighScoreInterface high_score(final int the_index) {
    // TODO setter high_score method stub
    return null;
  }

  public HighScoreInterface[] high_scores() {
    // TODO getter high_scores method stub
    return null;
  }

  public byte lives() {
    // TODO lives getter method stub
    return 0;
  }

  public int maximum_fuel() {
    // TODO maximum_fuel getter method stub
    return 0;
  }

  public void new_bonus(final int the_new_value) {
    // TODO new_bonus setter method stub
  }

  public boolean new_high_score(final HighScoreInterface the_high_score) {
    // TODO new_high_score method stub
    return false;
  }

  public int score() {
    // TODO score method stub
    return 0;
  }

}
