/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.entities.about;

/**
 * The state of the Thrust game, including current score, bonus, fuel, lives,
 * and high scores.
 *
 * @author simon markey,holly baker,ursula redmond (simon.markey@ucdconnect.ie)
 * @version 11 April 2008
 */
public class GameState {

  /** bonus.*/
  private transient int my_bonus;

  /**the current lives, initially 4.*/
  private transient byte my_lives;

  /**the initial fuel.*/
  private final transient int my_fuel;

  /**the maximum fuel.*/
  private final transient float my_maximum_fuel = Float.POSITIVE_INFINITY;
  /**the maximum fuel there can be.*/

  /**the initial score.*/
  private transient int my_score;

  /**an array containing the highscores.*/
  private final transient HighScoreInterface[] my_highScores;

  /**the amount of highscores there can be.*/

  /**
   * There are eight high scores.
   */
  public final static int MY_HIGH_SCORE_COUNT = 8;

  //@ invariant HIGH_SCORE_COUNT == 8;
  //@ invariant (* There are eight high scores. *);

  public GameState(final int the_initial_fuel, final byte the_initial_lives) {
    my_bonus = 0;
    my_lives = the_initial_lives;
    my_fuel = the_initial_fuel;
    my_score = 0;
    my_highScores = new HighScoreInterface[my_HIGH_SCORE_COUNT];
  }

  /**
   * @return What is the current bonus?
   * @bon BONUS What is your value?
   */
  //@ ensures 0 <= \result;
  public/*@ pure @*/int bonus() {
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

  //@ invariant (* Bonus values are always non-negative. *);
  //@ invariant 0 <= bonus();

  /**
   * @return How much fuel do you contain?
   * @idea The current fuel of the spaceship.
   * @note Note that the {@link thrust.entities.in_game.Spaceship}
   * class should be the actual owner of this data; this is just
   * a convenience method.
   */
  //@ ensures 0 <= \result;
  public/*@ pure @*/int current_fuel() {
    return my_fuel;

  }

  /**
   * @return How much fuel can you contain?
   * @idea The maximum fuel of the spaceship.
   */
  //@ ensures 0 <= \result;
  public/*@ pure @*/float maximum_fuel() {
    return my_maximum_fuel;
  }

  /**
   * @return What is the current score?
   */
  //@ ensures 0 <= \result;
  public/*@ pure @*/int score() {
    return my_score;

  }

  //@ invariant (* Score is always non-negative and finite. *);
  //@ invariant 0 <= score();

  /**
   * Change the current score by this many points.
   * @param some_new_points the new points to add to the current score.
   */
  //@ ensures score() == \old(score() + some_new_points);
  public void change_score(final int some_new_points) {
    my_score = my_score + some_new_points;
  }

  /**
   * @return How many lives do you have?
   */
  //@ ensures 0 <= \result;
  public/*@ pure @*/byte lives() {
    return my_lives;

  }

  //@ invariant (* Number of lives is always non-negative and finite. *);
  //@ invariant 0 <= lives();

  /**
   * @param some_new_lives Change the current lives by this many lives.
   */
  //@ ensures lives() == \old(lives() + some_new_lives);
  public/*@ pure @*/void change_lives(final byte some_new_lives) {
    my_lives += some_new_lives;
  }

  /**
   * @return What are the current high scores?
   */
  //@ ensures \result.length == HIGH_SCORE_COUNT;
  //@ ensures \nonnullelements(\result);
  public/*@ pure @*/HighScoreInterface[] high_scores() {
    for (int i = 0; i < my_highScores.length; i++) {

      for (int j = my_highScores.length; j > i; j--) {
        if (my_highScores[i].score() > my_highScores[j].score()) {
          final int temp = my_highScores[i].score();
          my_highScores[i].new_score(my_highScores[j].score());
          my_highScores[j].new_score(temp);

        }

      }
    }
    return my_highScores;
  }

  /*@ invariant (\forall int i, j; 0 <= i & i < j & j < HIGH_SCORE_COUNT &
    @            high_scores()[i].score() >= high_scores()[j].score());
    @ invariant (* High scores are ordered from high to low. *);
    @*/

  /*@ initially (* There is a fixed initial set of high scores. *);
    @ initially \nonnullelements(high_scores());
    @*/

  /**
   * @param the_index the index to lookup.
   * @return What is the high score at this index?
   */
  //@ requires 0 <= the_index & the_index < HIGH_SCORE_COUNT;
  //@ ensures \result.equals(high_scores()[the_index]);
  public/*@ pure non_null @*/HighScoreInterface high_score(final int the_index) {
    return my_highScores[the_index];
  }

  /**
   *
   * @param the_high_score the potential high score to check.
   * @return Is this score a new high score?
   */
  /*@ ensures \result <==> high_scores()[0].score() >= the_high_score.score() &
    @                      the_high_score.score() >= high_scores()[HIGH_SCORE_COUNT-1].score();
    @*/
  public/*@ pure @*/boolean new_high_score(
            final HighScoreInterface the_possible_new_high_score) {
    int lowest = my_highScores[0].my_score;

    for (int i = 0; i < my_highScores.length; i++) {
      if (lowest > my_highScores[i].my_score) {
        lowest = my_highScores[i].my_score;

      }
    }
    boolean answer;
    if (the_possible_new_high_score.my_score > lowest) {
      answer = true;
    } else {
      answer = false;
    }
    return answer;
  }

  /**
   * @param the_new_high_score
   *  Insert this score into the high score table.
   */
  /*@ ensures new_high_score(the_new_high_score) ==>
    @         (\exists int i; 0 <= i & i < HIGH_SCORE_COUNT;
    @          high_score(i).equals(the_new_high_score));
    @*/
  public void add_high_score(
            final /*@ non_null @*/HighScoreInterface the_new_high_score) {
//This adds a high score to the table.
  }

  /**
   * A pair of a sequence of three initials and a score.
   *
   * @author Joe Kiniry (kiniry@acm.org)
   * @version 11 April 2008
   */
  public class HighScoreInterface {
    /**
     * Stores the score.
     */
    private transient int my_score;
    /**
     * Stores the name.
     */
    private transient char[] my_name;
    /**
     * @return What is your score?
     */
    //@ ensures 0 <= \result;
    public/*@ pure @*/int score() {
      return my_score;
    }

    /**
     * @return What are your initials?
     */
    //@ ensures \result.length == 3;
    public/*@ pure @*/char[] initials() {
      return my_name;
    }

    /**
     * @param the_new_score This is your score.
     */
    //@ requires 0 <= the_new_score;
    //@ ensures score() == the_new_score;
    public void new_score(final int the_new_score) {
      if (the_new_score >= 0) {
        my_score = the_new_score;
      }
    }

    /**
     * @param the_new_initials These are your initials.
     */
    //@ requires the_new_initials.length == 3;
    //@ ensures initials().equals(\old(the_new_initials));
    public void new_initials(final /*@ non_null @*/char[] the_new_initials) {
      final int an_IN3 = 3;
      final int second = 2;
      if (the_new_initials.length == an_IN3) {
        my_name[0] = the_new_initials[0];
        my_name[1] = the_new_initials[1];
        my_name[second] = the_new_initials[second];
      }
    }

    //@ invariant (* High scores are always non-negative and finite. *);
    //@ invariant 0 <= score();

    //@ invariant (* Initials are always three characters in length. *);
    //@ invariant initials().length == 3;
  }
}
