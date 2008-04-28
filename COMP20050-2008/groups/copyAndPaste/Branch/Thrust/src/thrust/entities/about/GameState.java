package thrust.entities.about;
/**
 * The state of the Thrust game, including current score, bonus, fuel, lives,
 * and high scores.
 *
 * @author Patrick Nevin (patrick.nevin@ucdconnect.ie)
 * @version 20 April 2008
 */
public class GameState extends AbstractGameState {
  /**
   * The current bones.
   */
  private int my_bonus;
  /**
   * The current fuel.
   */
  private int my_fuel;
  /**
   * the max fuel.
   */
  private int my_max_fuel;
  /**
   * the current score.
   */
  private int my_current_score;
  /**
   * current amount of lives.
   */
  private byte my_lives;
  /**
   * An array of High scores.
   */
  private HighScoreClass[] my_high_scores;
  /**
   * A constructor to initialise instances of this object.
   * @param bonus
   * @param fuel
   * @param max_fuel
   * @param score
   * @param lives
   */
  public GameState() {
    this.my_high_scores = new HighScoreClass[HIGH_SCORE_COUNT];
  }
  /**
   * @return What is the current bonus?
   * @bon BONUS What is your value?
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ int bonus() {
    assert this.my_bonus >= 0 : "ERROR: bonus less than zero";
    return this.my_bonus;
  }
  /**
   * @param the_new_value This is your new value.
   */
  //@ requires 0 <= the_new_value;
  //@ ensures bonus() == the_new_value;
  public void new_bonus(final int the_new_value) {
    assert this.my_bonus == the_new_value : "ERROR:";
    this.my_bonus = the_new_value;
  }
  /**
   * @return How much fuel do you contain?
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ int current_fuel() {
    assert this.my_fuel >= 0 : "ERROR: Fuel non-negative";
    return this.my_fuel;
  }

  /**
   * @return How much fuel can you contain?
   */
  //@ ensures 0 <= \result;
  public  /*@ pure @*/ int maximum_fuel() {
    assert this.my_max_fuel >= 0 : "ERROR: Max Fuel non-negative";
    return this.my_max_fuel;
  }

  /**
   * @return What is the current score?
   */
  //@ ensures 0 <= \result;
  public  /*@ pure @*/ int score() {
    assert this.my_current_score >= 0 : "ERROR: Score non-negative";
    return this.my_current_score;
  }

  /**
   * Change the current score by this many points.
   * @param some_new_points the new points to add to the current score.
   */
  //@ ensures score() = \old(score() + some_new_points);
  public  void change_score(final int some_new_points) {
    this.my_current_score += some_new_points;
  }

  /**
   * @return How many lives do you have?
   */
  //@ ensures 0 <= \result;
  public  /*@ pure @*/ byte lives() {
    assert this.my_lives >= 0 : "ERROR: lives non-negative";
    return this.my_lives;
  }

  /**
   * @param some_new_lives Change the current lives by this many lives.
   */
  //@ ensures lives() == \old(lives() + some_new_lives);
  public  /*@ pure @*/ void change_lives(final byte some_new_lives) {
    this.my_lives += some_new_lives;
  }

  //@ public invariant HIGH_SCORE_COUNT == 8;
  //@ public invariant (* There are eight high scores. *);

  /**
   * @return What are the current high scores?
   */
  //@ ensures \result.length == HIGH_SCORE_COUNT;
  //@ ensures \nonnullelements(\result);
  public  /*@ pure \non null elements @*/ HighScoreInterface[] high_scores() {
    assert this.my_high_scores.length == HIGH_SCORE_COUNT : "ERROR:";

    for (int i = 0; i <= HIGH_SCORE_COUNT; i++) {
         assert this.my_high_scores[i] != null : "Error: Only non-nulls";
    }
    return this.my_high_scores;
  }

  /**
   * @param the_index the index to lookup.
   * @return What is the high score at this index?
   */
  //@ requires 0 <= the_index & the_index < HIGH_SCORE_COUNT;
  //@ ensures \result.equals(high_scores()[the_index]);
  public HighScoreInterface high_score(final int the_index) {
    return this.my_high_scores[the_index];
  }
  /**
  *
  * @param the_high_score the potential high score to check.
  * @return Is this score a new high score?
  */
 /*@ ensures \result <==> high_scores()[0].score() >= the_high_score.score() &
   @                      the_high_score.score() >= high_scores()[HIGH_SCORE_COUNT-1].score();
   @*/
  public boolean new_high_score(final HighScoreInterface the_pos_new_high) {
    return (this.my_high_scores[0].my_score == the_pos_new_high.score());
  }
  /**
   * @param the_new_high_score Insert this score into the high score table.
   */
  /*@ ensures new_high_score(the_new_high_score) ==>
    @         (\exists int i; 0 <= i & i < HIGH_SCORE_COUNT;
    @          high_score(i).equals(the_new_high_score));
    @*/
  public  void add_high_score(final HighScoreInterface the_new_high_score) {
    for (int i = 0; i < HIGH_SCORE_COUNT - 1; i++) {
      if (this.my_high_scores[i].my_score <= the_new_high_score.score()) {
        this.my_high_scores[i] = (HighScoreClass)the_new_high_score;
      }
    }
  }
  /**
   * A pair of a sequence of three initials and a score.
   *
   * @author Patrick Nevin (Patrick Nevin: 06754155)
   * @version 11 April 2008
   */
  private class HighScoreClass implements HighScoreInterface {
    /**
     *An array of size 3 to hold initials.
     */
    private char[] my_initialsArray = new char[MY_SIZE];
    /**
     *score associated with player with initials.
     */
    private int my_score;
    /**
     * @return What is your score?
     */
    //@ ensures 0 <= \result;
    public /*@ pure @*/ int score() {
      assert this.my_score >= 0 : "Score must be >= zero";
      return this.my_score;
    }

    /**
     * @return What are your initials?
     */
    //@ ensures \results.length == 3;
    public /*@ pure \non-null-elements @*/ char[] initials() {
      assert this.my_initialsArray.length == MY_SIZE : "Array not length 3";
      return this.my_initialsArray;
    }

    /**
     * @param the_new_score This is your score.
     */
    //@ requires 0 <= the_new_score;
    //@ ensures score() == the_new_score;
    public void new_score(final int a_new_score) {
      this.my_score = a_new_score;
    }

    /**
     * @param the_new_initials These are your initials.
     */
    //@ requires the_new_intials.length == 3;
    //@ ensures initials().equals(\old(the_new_initials));
    public void new_initials(final/*@ non_null @*/ char[] a_new_initials) {
      this.my_initialsArray = a_new_initials;
    }
  }
}
