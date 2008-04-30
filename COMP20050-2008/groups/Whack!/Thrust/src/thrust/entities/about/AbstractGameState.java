
package thrust.entities.about;

import thrust.entities.in_game.Spaceship;
import thrust.entities.in_game.GameStateWhack.HighScoreInterface;

/**
 * The state of the Thrust game, including current score, bonus, fuel, lives,
 * and high scores.
 *
 * @author David Maguire (David.Maguire.2@ucdconnect.ie)
 * @version 11 April 2008
 */

public abstract /*@ pure @*/ class AbstractGameState {
  /**the current bonus.*/
  private int my_bonus;
  /**the initial lives.*/
  private byte my_lives;
  /**the initial fuel.*/
  private int my_fuel;
  /**the max fuel.*/
  private int my_max_fuel;
  /**the maximum fuel there can be.*/
  private final int my_maximum_fuel = 9999;
  /**the initial score.*/
  private int my_score;
  /**an array containing the highscores.*/
  private HighScoreInterface[] my_highScores;
  /**the amount of highscores there can be.*/
  private final int my_highscore_number = 8;

  public AbstractGameState(final int the_initial_fuel,
                        final byte the_initial_lives) {
    my_bonus = 0;
    my_lives = the_initial_lives;
    my_fuel = the_initial_fuel;
    my_max_fuel = my_maximum_fuel;
    my_score = 0;
    my_highScores = new HighScoreInterface[my_highscore_number];
  }
  /**
   * @return What is the current bonus?
   * @bon BONUS What is your value?
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ int bonus() {
    return my_bonus;
  }

  /**
   * @param the_new_value This is your new value.
   */
  //@ requires 0 <= the_new_value;
  //@ ensures bonus() == the_new_value;
  public void new_bonus(final int the_new_value) {
    if (the_new_value >= 0) {
      my_bonus = the_new_value;
    }
  }

  /**
   * @return How much fuel do you contain?
   * @design The current fuel of the spaceship.
   * @note Note that the {@link Spaceship} class should be the
   * actual owner of this data; this is just a convenience method.
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ int current_fuel() {
    return my_fuel;
  }

  /**
   * @return How much fuel can you contain?
   * @design The maximum fuel of the spaceship.
   */
  //@ ensuress 0 <= \result;
  public /*@ pure @*/ int maximum_fuel() {
    return my_max_fuel;
  }

  /**
   * @return What is the current score?
   */
  //@ ensures 0 <= \result;
  public/*@ pure @*/ int score() {
    return my_score;
  }

  /**
   * Change the current score by this many points.
   * @param some_new_points the new points to add to the current score.
   */
  //@ ensures score() = \old(score() + some_new_points);
  public void change_score(final int some_new_points) {
    my_score = my_score + some_new_points;
  }

  /**
   * @return How many lives do you have?
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ byte lives() {
    return my_lives;
  }

  /**
   * @param some_new_lives Change the current lives by this many lives.
   */
  //@ ensures lives() == \old(lives() + some_new_lives);
  public /*@ pure @*/ void change_lives(final byte some_new_lives) {
    my_lives = my_lives + some_new_lives;

  }

  //@ public invariant HIGH_SCORE_COUNT == 8;
  //@ public invariant (* There are eight high scores. *);

  /**
   * @return What are the current high scores?
   */
  //@ ensures \result.length == HIGH_SCORE_COUNT;
  /*@ ensures (\forall int i, int j; 0 <= i & i < j & j < HIGH_SCORE_COUNT &
    @          \result[i] >= \result[j]);
    @ ensures (* High scores are ordered from high to low. *);
    @*/
  public /*@ pure \nonnullelements @*/ HighScoreInterface[] high_scores() {
    for (int i = 0; i < my_highScores.length; i++) {
      for (int j = my_highScores.length; j >= i; --j) {
        if (my_highScores[i].score() > my_highScores[j].score()) {
          final int temp = my_highScores[i].score();
          my_highScores[i].new_score(my_highScores[j].score());
          my_highScores[j].new_score(temp);
        }
      }
    }
    return my_highScores;

  }

  public /*@ pure non_null @*/HighScoreInterface high_score(final int the_index) {
    return my_highScores[the_index];
  }

  public /*@ pure @*/ boolean new_high_score(/*@ non_null */
                                             final HighScoreInterface
                                             the_possible_new_high_score) {
    int min = my_highScores[0].my_score;
    for (int i = 0; i < my_highScores.length; i++) {
      if (min > my_highScores[i].my_score) {
        min = my_highScores[i].my_score;
      }
    }
    if (the_possible_new_high_score.my_score > min) {
      return true;
    }
    return false;
  }

  public void add_high_score(/*@ non_null @*/
  final HighScoreInterface the_new_high_score) {
    final int score = the_new_high_score.my_score;
    for (int i = 0; i < my_highScores.length; i++) {
      if (my_highScores[i].my_score < score) {
        for (int j = my_highScores.length; j >= i; --j) {
          my_highScores[j] = my_highScores[j - 1];
        }
      }
      my_highScores[i] = the_new_high_score;
    }
  }

  /**
   * A pair of a sequence of three initials and a score.
   *
   * @author David Maguire (David.Maguire.2@ucdconnect.ie)
   * @version 14 April 2008
   */
  public /*@ pure @*/ class HighScoreInterface {
    /**the score.*/
    private int my_score;
    /**an int holding the number two.*/
    private final int my_two = 2;
    /**an int holding the number three.*/
    private final int my_three = 3;
    /**the name.*/
    private char[] my_name;
    /**
     * @return What is your score?
     */
    //@ ensures 0 <= \result;
    /*@ pure @*/ public int score() {
      return my_score;
    }
    /**
     * @return What are your initials?
     */
    //@ ensures \results.length == 3;
    /*@ pure \nonnullelements @*/ public char[] initials() {
      return my_name;
    }


    /**
     * @param the_new_score This is your score.
     */
    //@ requires 0 <= the_new_score;
    //@ ensures score() == the_new_score;
    void new_score(final int the_new_score) {
      if (the_new_score >= 0) {
        my_score = the_new_score;
      }
    }


    /**
     * @param the_new_initials These are your initials.
     */
    //@ requires the_new_intials.length == 3;
    //@ ensures initials().equals(\old(the_new_initials));
    void new_initials(/*@ non_null @*/ final char[] the_new_initials) {

      if (the_new_initials.length == my_three) {
        my_name[0] = the_new_initials[0];
        my_name[1] = the_new_initials[1];
        my_name[my_two] = the_new_initials[my_two];
      }
    }
  }

  public void add_high_score(final int the_new_high_score) {
    if (new_high_score(the_new_high_score)) {
      my_score = the_new_high_score;
    }

  }

  public boolean new_high_score(final int the_possible_new_high_score) {
    boolean my_highscore = false;
    if (the_possible_new_high_score > my_score) {
      my_highscore = true;
    }
    return my_highscore;
  }

}
