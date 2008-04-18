package thrust.entities.in_game;

import java.util.Scanner;

//import java.lang.reflect.Array;

/**
 * @author Ciaran Hale (ciaran.hale@ucd.ie)
 * @author Colin Casey (colin.casey@org.com)
 * @version 17 April 2008
 */
public class GameState extends AbstractGameState {

  /** The bonus points associated with finishing a level. */
  private static int my_bonus;
  /** The current score of a player. */
  private static int my_score;
  /** The number of lives a player has left. */
  private static byte my_lives;

  public int bonus() {
    return my_bonus;
  }

  public void new_bonus(final int the_new_value) {
    my_bonus = the_new_value;
  }

  public int current_fuel() {
    return current_fuel();
    //have to make it implement the fuelable method
    //and return the current fuel

  }

  public int maximum_fuel() {
    final int max = 9999;
    return  max;

  }

  public int score() {
    return my_score;
  }

  public void change_score(final int some_new_points) {
    my_score = my_score + some_new_points;
  }

  public byte lives() {
    return my_lives;
  }

  public void change_lives(final byte some_new_lives) {
    my_lives = (byte) (my_lives + some_new_lives);
  }

  public HighScoreInterface[] high_scores() {
    return null;

  }

  public HighScoreInterface high_score(final int the_index) {
    return null;

  }

  public boolean new_high_score(final HighScoreInterface the_high_score) {
    return false;

  }

  public void add_high_score(final HighScoreInterface the_new_high_score) {

  }
  /**
   * @author Ciaran Hale (ciaran.hale@ucd.ie)
   * @author Colin Casey (colin.casey@org.com)
   * @version 17 April 2008
   */
  public abstract class AbstractHighScore implements HighScoreInterface {

    public int score() {
      return 0;

    }

    public final char[] initials() {
      return null;

    }

    public void new_score(final int the_new_score) {

    }

    public void new_initials(final char[] the_new_initials) {
      final Scanner scan = new Scanner(System.in);
      final String a = scan.next();
      final int max = 6;
      final  String b = a;
      if (a.length() > max)
      {
        final char[] array = {b.charAt(0), b.charAt(1), b.charAt(2),
          b.charAt(3), b.charAt(4), b.charAt(5), b.charAt(6) };
        for (int all = 0; all < max; all++)
        {
          System.out.print(array[all]);
        }
      }
    }
  }
}
