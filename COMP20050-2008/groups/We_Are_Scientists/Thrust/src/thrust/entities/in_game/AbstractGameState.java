/**
 * 
 */
package thrust.entities.in_game;

/**
 * The state of the Thrust game, including current score, bonus, fuel, lives,
 * and high scores.
 *
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 11 April 2008
 */

public abstract /*@ pure @*/ class AbstractGameState {
  /**
   * @return What is the current bonus?
   * @bon BONUS What is your value?
   */
  //@ ensures 0 <= \result;
  public abstract /*@ pure @*/ int bonus();

  /**
   * @param the_new_value This is your new value.
   */
  //@ requires 0 <= the_new_value;
  //@ ensures bonus() == the_new_value;
  public abstract void new_bonus(int the_new_value);

  /**
   * @return How much fuel do you contain?
   * @design The current fuel of the spaceship.
   * @note Note that the {@link Spaceship} class should be the 
   * actual owner of this data; this is just a convenience method.
   */
  //@ ensures 0 <= \result;
  public abstract /*@ pure @*/ int current_fuel();

  /**
   * @return How much fuel can you contain?
   * @design The maximum fuel of the spaceship.
   */
  //@ ensures 0 <= \result;
  public abstract /*@ pure @*/ int maximum_fuel();

  /**
   * @return What is the current score?
   */
  //@ ensures 0 <= \result;
  public abstract /*@ pure @*/ int score();

  /**
   * Change the current score by this many points.
   * @param some_new_points the new points to add to the current score.
   */
  //@ ensures score() = \old(score() + some_new_points);
  public abstract void change_score(int some_new_points);

  /**
   * @return How many lives do you have?
   */
  //@ ensures 0 <= \result;
  public abstract /*@ pure @*/ byte lives();

  /**
   * @param some_new_lives Change the current lives by this many lives.
   */
  //@ ensures lives() == \old(lives() + some_new_lives);
  public abstract /*@ pure @*/ void change_lives(byte some_new_lives);

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
  public abstract /*@ pure \nonnullelements @*/ HighScoreInterface[] high_scores();

  public abstract /*@ pure non_null @*/ HighScoreInterface high_score(int the_index);

  public abstract /*@ pure @*/ boolean new_high_score(/*@ non_null @*/ HighScoreInterface the_possible_new_high_score);

  public abstract void add_high_score(/*@ non_null @*/ HighScoreInterface the_new_high_score);

  /**
   * A pair of a sequence of three initials and a score.
   *
   * @author Joe Kiniry (kiniry@acm.org)
   * @version 11 April 2008
   */
  public /*@ pure @*/ interface HighScoreInterface {
    /**
     * @return What is your score?
     */
    //@ ensures 0 <= \result;
    /*@ pure @*/ int score();

    /**
     * @return What are your initials?
     */
    //@ ensures \results.length == 3;
    /*@ pure \nonnullelements @*/ char[] initials();

    /**
     * @param the_new_score This is your score.
     */
    //@ requires 0 <= the_new_score;
    //@ ensures score() == the_new_score;
    void new_score(int the_new_score);

    /**
     * @param the_new_initials These are your initials.
     */
    //@ requires the_new_intials.length == 3;
    //@ ensures initials().equals(\old(the_new_initials));
    void new_initials(/*@ non_null @*/ char[] the_new_initials);
  }
}
