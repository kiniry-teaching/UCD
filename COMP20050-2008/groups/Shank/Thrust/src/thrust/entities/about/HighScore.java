package thrust.entities.about;

/**
 * @author Ben Fitzgerald (ben.fitz@hotmail.com)
 * @version 28 April 2008
 * */
public class HighScore implements AbstractGameState.HighScoreInterface {

  /**The array of initials.*/
  private char[] my_initials;
  /**The new inputed highscore.*/
  private int my_new_score;

  /**
   * @return What are your initials?
   * */
  public char[] initials() {
    return my_initials;
  }

  /**
   * @param These are your initials.
   * */
  public void new_initials(final char[] the_new_initials) {
    my_initials = the_new_initials;
  }

  /**
   * @param This is your score.
   * */
  public void new_score(final int the_new_score) {
    my_new_score = the_new_score;
  }

  /**
   * @return What is your score?
   * */
  public int score() {
    return my_new_score;
  }
}
