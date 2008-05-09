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

//import thrust.entities.about.AbstractGameState.HighScoreInterface;
import thrust.entities.in_game.Spaceship;

/**
 * The state of the Thrust game, including current score, bonus, fuel, lives,
 * and high scores.
 *
 * @author simon markey,holly baker,ursula redmond (simon.markey@ucdconnect.ie)
 * @version 11 April 2008
 */
public class GameState extends AbstractGameState {

  /** The game state. */
  private static byte my_state;

  /** Initial lives the player has. */
  private static final byte INIT_LIVES = 4;

  /** The number of points required to gain a life. */
  //private static final int NEW_LIFE_POINTS = 10000;

  /** Bonus at end of level.*/
  private transient int my_bonus;

  /** The current lives the player has. */
  private transient byte my_lives = INIT_LIVES;

  /** The current fuel of the spaceship. */
  private final transient int my_fuel = Spaceship.INITIAL_FUEL;

  /** The maximum fuel.*/
  private final transient float my_maximum_fuel = Float.POSITIVE_INFINITY;

  /** The initial score.*/
  private transient int my_score;

  /** An array containing the high scores.*/
  private final transient HighScoreInterface[] my_highScores;

  /** There are eight high scores. */
  //private static final int MY_HIGH_SCORE_COUNT = 8;

  //@ invariant HIGH_SCORE_COUNT == 8;
  //@ invariant (* There are eight high scores. *);

  public GameState() {
    super();
    my_bonus = 0;
    my_score = 0;
    my_highScores = new HighScoreInterface[AbstractGameState.HIGH_SCORE_COUNT];
  }

  /**
   * @return What is the current bonus?
   * @bon BONUS What is your value?
   */
  //@ ensures 0 <= \result;
  public int bonus() {
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
  public int current_fuel() {
    return my_fuel;
  }

  /**
   * @return How much fuel can you contain?
   * @idea The maximum fuel of the spaceship.
   */
  //@ ensures 0 <= \result;
  public int maximum_fuel() {
    return (int) my_maximum_fuel;
  }

  /**
   * @return What is the current score?
   */
  //@ ensures 0 <= \result;
  public int score() {
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
  public byte lives() {
    return my_lives;
  }

  //@ invariant (* Number of lives is always non-negative and finite. *);
  //@ invariant 0 <= lives();

  /**
   * @param some_new_lives Change the current lives by this many lives.
   */
  //@ ensures lives() == \old(lives() + some_new_lives);
  public void change_lives(final byte some_new_lives) {
    my_lives = (byte) (my_lives + some_new_lives);
  }

  /**
   * @return What are the current high scores?
   */
  //@ ensures \result.length == HIGH_SCORE_COUNT;
  //@ ensures \nonnullelements(\result);
  public HighScoreInterface[] high_scores() {
    return (HighScoreInterface[])my_highScores.clone();
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
  public HighScoreInterface high_score(final int the_index) {
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
  public boolean new_high_score(
            final HighScoreInterface the_possible_new_high_score) {

    int lowest = my_highScores[0].score();

    for (int i = 0; i < HIGH_SCORE_COUNT - 1; i++) {
      if (my_highScores[i] != null && lowest > my_highScores[i].score()) {
        lowest = my_highScores[i].score();
      }
    }

    boolean answer;
    if (the_possible_new_high_score.score() > lowest) {
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
    for (int i = 0; i < HIGH_SCORE_COUNT - 1; i++) {
      if (my_highScores[i] != null && my_score > my_highScores[i].score() &&
          i > 0) {
        my_highScores[i - 1] = my_highScores[i];
      } else {
        my_highScores[i] = the_new_high_score;
      }
    }
  }

  /**
   * Sets the state.
   * @param the_new_state The new state
   */
  public void set_state(final byte the_new_state) {
    my_state = the_new_state;
  }

  /**
   * Returns the state.
   * @return The state
   */
  public byte get_state() {
    return my_state;
  }
}
