package thrust.display;

import java.io.File;
import java.io.IOException;
import java.io.BufferedInputStream;
import java.io.FileInputStream;
import java.io.DataInputStream;
/**
 * Top scores of past players.
 *
 * @author Eoin Healy (eoin.healy@gmail.com)
 * @version 11 April 2008
 */

public class HighScore extends AbstractHighScoreDisplay {
  /**
   *  An object to combine the name and score of a person.
   */
  private class StoreScore {
    /** The users name. */
    String my_name;

    /** The users score. */
    int my_score;

    public StoreScore(final String a_name, final int a_score) {
      my_name = a_name;
      my_score = a_score;
    }
  }
  /** The length of the name associated with the score. */
  private static final int MAXCHARS = 3;
  /** The amount of highscores. */
  private static final int MAXSCORES = 3;

  /** The top MAXSCORES scores. */
  private static StoreScore[] top8 = new StoreScore[MAXSCORES];
  /**
   * @param a_name The users name.
   * @param a_score The users score.
   */
  //@ invariant (* Score is always non-negative and finite. *);
  //@ invariant 0 <= a_score();
  public void add_new_high_score(final String a_name, final int a_score) {
    if (a_score > top8[top8.length - 1].my_score) {
      top8[top8.length - 1] = new StoreScore(a_name, a_score);
      sortHighScores();
      //write to file
    }
  }

  public void display() {
    //@ assert !displayed();
    /* Temp Code */
    for (int i = 0; i < top8.length; i++) {
      assert true;
    }
    //@ assert displayed();
  }

  public boolean displayed() {
    return false;
  }

  public void hide() {
    //@ assert displayed();
    //@ assert !displayed();
  }

  public void sortHighScores() {
    // Sorting done here, bubble sort for testing;
    assert true;
  }

  public void readInScores() {
    DataInputStream dis = null;
    try {
      final File highscores = new File("filename");

      final FileInputStream highscoresFileStream =
          new FileInputStream(highscores);
      final BufferedInputStream hsStream =
          new BufferedInputStream(highscoresFileStream);
      dis = new DataInputStream(hsStream);
      for (int i = 0; i < MAXSCORES; i++) {
        for (int j = 0; j < MAXCHARS; j++) {
          top8[i].my_name = top8[i].my_name + dis.readChar();
        }
        top8[i].my_score = dis.readInt();
      }

    } catch (IOException e) {
      e.printStackTrace();
    }
  }
}
