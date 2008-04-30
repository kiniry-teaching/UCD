package thrust.display;
/**
 * @author David Maguire (David.Maguire.2@ucdconnect.ie)
 * @version 14 April 2008
 */
public class HighScore extends AbstractHighScoreDisplay {

 /* public class Hiscores {
    int[] scores;
    String[] names;

    public Hiscores() {
      scores = new int[8];
      names = new String[8];
    }
  }*/
  /**boolean that holds whether or not the high score is displayed.*/
  private boolean my_displayed;
  /**
   * @return Are the high scores currently displayed?"
   */
  public boolean displayed() {
    return my_displayed;
  }

  /**
   * Display the high scores.
   */
  public void display() {
    if (!my_displayed) {
      my_displayed = true;
    }

  }

  /**
   * Hide the high scores.
   */
  //@ ensures !displayed();
  public void hide() {
    if (my_displayed) {
      my_displayed = false;
    }

  }

  /**
   * Permit the player to add a new name for this high score.
   */
  public void add_new_high_score() {


  }
}
