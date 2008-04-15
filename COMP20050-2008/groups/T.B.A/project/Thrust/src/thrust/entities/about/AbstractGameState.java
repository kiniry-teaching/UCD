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
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 11 April 2008
 */
public abstract class AbstractGameState {
  /**
   * There are eight high scores.
   */
  public static final int HIGH_SCORE_COUNT = 8;
  //@ invariant HIGH_SCORE_COUNT == 8;
  //@ invariant (* There are eight high scores. *);

  /**
   * Stores a bonus value.
   */
  private int my_bonus;
  //@ ensures 0 <= bonus;

  /**
   * Stores a fuel value.
   */
  private int my_fuel;
  //@ ensures 0 <= myfuel;

  /**
   * Stores the current score.
   */
  private int my_score;
  //@ ensures 0 <= my_score;

  /**
   * Stores the highScore in an array.
   */
  private HighScoreInterface the_highScore[];
  //@ ensures 0 <= highScore;

  /**
   * Stores the current number of lives.
   */
  private byte my_lives;
  //@ ensures 0 <= lives;

  /**
   * @return What is the current bonus?
   * @bon BONUS What is your value?
   */

  public /*@ pure @*/ int bonus()
  {
    return my_bonus;
  }
  //@ ensures 0 <= \result;
  
  /**
   * @param the_new_value This is your new value.
   */
  //@ requires 0 <= the_new_value;
  //@ ensures bonus() == the_new_value;
  public void new_bonus(final int the_new_value)
  {
    my_bonus = the_new_value;
  }
  //@ invariant (* Bonus values are always non-negative. *);
  //@ invariant 0 <= bonus();

  /**
   * @return How much fuel do you contain?
   * @idea The current fuel of the spaceship.
   * @note Note that the {@link Spaceship} class should be the
   * actual owner of this data; this is just a convenience method.
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ int current_fuel()
  {
    return my_fuel;
  }

  /**
   * @return How much fuel can you contain?
   * @idea The maximum fuel of the spaceship.
   */
  //@ ensures 0 <= \result;
  public  /*@ pure @*/  int maximum_fuel()
  {
    final int the_max_feul = 2000;
    return the_max_feul;
  }

  /**
   * @return What is the current score?
   */
  //@ ensures 0 <= \result;
  public  /*@ pure @*/  int score()
  {
    return my_score;
  }

  //@ invariant (* Score is always non-negative and finite. *);
  //@ invariant 0 <= score();

  /**
   * Change the current score by this many points.
   * @param some_new_points the new points to add to the current score.
   */
  //@ ensures score() == \old(score() + some_new_points);
  public void change_score(final int some_new_points)
  {
    my_score = some_new_points;
  }

  /**
   * @return How many lives do you have?
   */
  //@ ensures 0 <= \result;
  public  /*@ pure @*/  byte lives()
  {
    return my_lives;
  }

  //@ invariant (* Number of lives is always non-negative and finite. *);
  //@ invariant 0 <= lives();

  /**
   * @param some_new_lives Change the current lives by this many lives.
   */
  //@ ensures lives() == \old(lives() + some_new_lives);
  public /*@ pure @*/ void change_lives(final byte some_new_lives)
  {
    my_lives = some_new_lives;
  }

  /**
   * @return What are the current high scores?
   */
  //@ ensures \result.length == HIGH_SCORE_COUNT;
  //@ ensures \nonnullelements(\result);
  public /*@ pure @*/ HighScoreInterface[] high_scores()
  {
    return the_highScore;
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
  public abstract /*@ pure non_null @*/
  HighScoreInterface high_score(int the_index);

  /**
   *
   * @param the_high_score the potential high score to check.
   * @return Is this score a new high score?
   */
  /*@ ensures \result <==> high_scores()[0].score() >= the_high_score.score() &
    @                      the_high_score.score() >= high_scores()[HIGH_SCORE_COUNT-1].score();
    @*/
  public abstract /*@ pure @*/
  boolean new_high_score(/*@ non_null @*/ HighScoreInterface the_high_score);

  /**
   * @param the_new_high_score Insert this score into the high score table.
   */
  /*@ ensures new_high_score(the_new_high_score) ==>
    @         (\exists int i; 0 <= i & i < HIGH_SCORE_COUNT;
    @          high_score(i).equals(the_new_high_score));
    @*/
  public abstract void
  add_high_score(/*@ non_null @*/ HighScoreInterface the_new_high_score);

  /**
   * A pair of a sequence of three initials and a score.
   *
   * @author Joe Kiniry (kiniry@acm.org)
   * @version 11 April 2008
   */
  public interface HighScoreInterface {
    /**
     * @return What is your score?
     */
    //@ ensures 0 <= \result;
    /*@ pure @*/ int score();

    /**
     * @return What are your initials?
     */
    //@ ensures \result.length == 3;
    /*@ pure @*/ char[] initials();

    /**
     * @param the_new_score This is your score.
     */
    //@ requires 0 <= the_new_score;
    //@ ensures score() == the_new_score;
    void new_score(int the_new_score);

    /**
     * @param the_new_initials These are your initials.
     */
    //@ requires the_new_initials.length == 3;
    //@ ensures initials().equals(\old(the_new_initials));
    void new_initials(/*@ non_null @*/ char[] the_new_initials);

    //@ invariant (* High scores are always non-negative and finite. *);
    //@ invariant 0 <= score();

    //@ invariant (* Initials are always three characters in length. *);
    //@ invariant initials().length == 3;
  }
}
