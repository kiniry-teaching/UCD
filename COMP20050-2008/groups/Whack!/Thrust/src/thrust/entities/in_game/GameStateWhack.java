package thrust.entities.in_game;

import thrust.entities.in_game.AbstractGameState.HighScoreInterface;

/**
 * @author Tara Flood (0361188@ucdconnect.ie)
 * @version 14 April 2008
 */
public class GameStateWhack extends AbstractGameState {

  /**
   * @return What is the current bonus?
   * @bon BONUS What is your value?
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ int bonus() {
    return 1;
  }

  /**
   * @param the_new_value This is your new value.
   */
  //@ requires 0 <= the_new_value;
  //@ ensures bonus() == the_new_value;
  public void new_bonus(final int the_new_value) {
  }

  /**
   * @return How much fuel do you contain?
   * @design The current fuel of the spaceship.
   * @note Note that the {@link Spaceship} class should be the
   * actual owner of this data; this is just a convenience method.
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ int current_fuel() {
    return 1;
  }

  /**
   * @return How much fuel can you contain?
   * @design The maximum fuel of the spaceship.
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ int maximum_fuel() {
    return 1;
  }

  /**
   * @return What is the current score?
   */
  //@ ensures 0 <= \result;
  public/*@ pure @*/ int score() {
    return 1;
  }

  /**
   * Change the current score by this many points.
   * @param some_new_points the new points to add to the current score.
   */
  //@ ensures score() = \old(score() + some_new_points);
  public void change_score(final int some_new_points) {
  }

  /**
   * @return How many lives do you have?
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ byte lives() {
    return 0;
  }

  /**
   * @param some_new_lives Change the current lives by this many lives.
   */
  //@ ensures lives() == \old(lives() + some_new_lives);
  public /*@ pure @*/ void change_lives(final byte some_new_lives) {

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
  public /*@ pure \nonnullelements @*/
  HighScoreInterface[] high_scores() {
  }

  public /*@ pure non_null @*/
  HighScoreInterface high_score(final int the_index) {
  }

  public /*@ pure @*/ boolean new_high_score(/*@ non_null */
                                             final HighScoreInterface
                                             the_possible_new_high_score) {
    return true;
  }

  public void add_high_score(/*@ non_null @*/
  final HighScoreInterface the_new_high_score) {
  }

  /**
   * A pair of a sequence of three initials and a score.
   *
   * @author Tara Flood (06361188@ucdconnect.ie)
   * @version 14 April 2008
   */
  public /*@ pure @*/ class HighScoreInterface {
    /**
     * @return What is your score?
     */
    //@ ensures 0 <= \result;
    /*@ pure @*/ public int score() {
      return 1;
    }
    /**
     * @return What are your initials?
     */
    //@ ensures \results.length == 3;
    /*@ pure \nonnullelements @*/ public char[] initials() {
      return a;
    }


    /**
     * @param the_new_score This is your score.
     */
    //@ requires 0 <= the_new_score;
    //@ ensures score() == the_new_score;
    void new_score(final int the_new_score) {
    }


    /**
     * @param the_new_initials These are your initials.
     */
    //@ requires the_new_intials.length == 3;
    //@ ensures initials().equals(\old(the_new_initials));
    void new_initials(/*@ non_null @*/ final char[] the_new_initials) {

    }
  }

  public void add_high_score(
                             thrust.entities.in_game.AbstractGameState.HighScoreInterface 
                             the_new_high_score) {
    // TODO Auto-generated method stub

  }

  public boolean new_high_score(
                                final thrust.entities.in_game.AbstractGameState.HighScoreInterface
                                the_possible_new_high_score) {
    // TODO Auto-generated method stub
    return false;
  }
}
