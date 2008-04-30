package thrust.entities.about;

/**
 * A pair of a sequence of three initials and a score.
 *
 * @author Joe Kiniry (kiniry@acm.org)
 * @ author Nick and Steve
 * @version 11 April 2008
 */
public interface HighScoreInterface {
  /**
   * There are eight high scores.
   */
  int HIGH_SCORE_COUNT = 8;
  //@ invariant HIGH_SCORE_COUNT == 8;
  //@ invariant (* There are eight high scores. *);
  // put 8 here, HIGH_SCORE_COUNT wasn't being read-Steve
  /**
   * @return What is the current score?
   */
  //@ ensures 0 <= \result;
  /*@ pure @*/ int score();

  //@ invariant (* Score is always non-negative and finite. *);
  //@ invariant 0 <= score();

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

  /**
   * Change the current score by this many points.
   * @param some_new_points the new points to add to the current score.
   */
  //@ ensures score() == \old(score() + some_new_points);

  void change_score(int some_new_points);

  /**
   * @return What are the current high scores?
   */
  //@ ensures \result.length == HIGH_SCORE_COUNT;
  //@ ensures \nonnullelements(\result);
  /*@ pure @*/ int[] high_scores();

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
  /*@ pure non_null @*/
  int high_score(int the_index);

  /**
   *
   * @param the_high_score the potential high score to check.
   * @return Is this score a new high score?
   */
  /*@ ensures \result <==> high_scores()[0].score() >= the_high_score.score() &
    @                      the_high_score.score() >= high_scores()[HIGH_SCORE_COUNT-1].score();
    @*/
  /*@ pure @*/
  boolean new_high_score(/*@ non_null @*/ int the_high_score);

  /**
   * @param the_new_high_score Insert this score into the high score table.
   */
  /*@ ensures new_high_score(the_new_high_score) ==>
    @         (\exists int i; 0 <= i & i < HIGH_SCORE_COUNT;
    @          high_score(i).equals(the_new_high_score));
    @*/
  void add_high_score(/*@ non_null @*/ int the_new_high_score);
}

