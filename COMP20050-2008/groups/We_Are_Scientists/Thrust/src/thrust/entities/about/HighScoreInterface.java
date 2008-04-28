package thrust.entities.about;

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
