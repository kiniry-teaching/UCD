package thrust.entities.in_game;



/**
 *
 * @author "Daire O'Doherty 06535691 (daireod@gmail.com)"
 * @version 20 April 2008
 *
 */

public  /*@ pure @*/ class GameState extends AbstractGameState {
  /** current score of the player.*/
  private int my_score;
 /** the bonus recieved by the player.*/
  private int my_bonus;
 /** the current amount of lives of the player.*/
  private byte my_amt_lives;
 /** the current fuel of the spaceship.*/
  private int my_fuel;
 /** the maximum fuel that the spaceship can contain.*/
  private final int my_maxi = 100;
  /** number of highscores.*/
  private final int my_high_score_count = 8;
 /**all of the highscores within the game.*/
  private HighScoreInterface[]my_high_scores = new HighScore[my_high_score_count];


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
    my_bonus = the_new_value;
  }


  //@ ensures 0 <= \result;
  public /*@ pure @*/ int current_fuel() {
    return my_fuel;
  }
  //@ ensures 0 <= \result;
  public /*@ pure @*/ int maximum_fuel() {
    return my_maxi;
  }
  //@ ensures 0 <= \result;
  public /*@ pure @*/ int score() {
    return my_score;
  }

  //@ ensures score() = \old(score() + some_new_points);
  public void change_score(final int some_new_points) {
    my_score += some_new_points;
  }

  /**
   * @return How many lives do you have?
   */
  //@ ensures 0 <= \result;
  public/*@ pure @*/ byte lives() {
    return my_amt_lives;
  }

  /**
   * @param some_new_lives Change the current lives by this many lives.
   */
  //@ ensures lives() == \old(lives() + some_new_lives);
  public /*@ pure @*/ void change_lives(final byte some_new_lives) {
    my_amt_lives += some_new_lives;
  }

  //@ public invariant HIGH_SCORE_COUNT == 8;
  //@ public invariant (* There are eight high scores. *);

  //@ ensures \result.length == HIGH_SCORE_COUNT;
  /*@ ensures (\forall int i, int j; 0 <= i & i < j & j < HIGH_SCORE_COUNT &
    @          \result[i] >= \result[j]);
    @ ensures (* High scores are ordered from high to low. *);
    @*/
  public /*@ pure \nonnullelements @*/ HighScoreInterface[] high_scores() {
    return my_high_scores;
  }

  public HighScoreInterface high_score(final int the_index) {
    return my_high_scores[the_index];
  }

  public boolean new_high_score(final HighScoreInterface the_poss_high_score) {
    for (int i = my_high_scores.length; i > 0; i--) {
      if (my_high_scores[i] != null) {
        if (my_score > my_high_scores[i].score()) {
          return true;
        }
      }
    }
    return false;
  }

  public void add_high_score(final HighScoreInterface the_new_high_score) {
    for (int i = 0; i < my_high_score_count; i++) {
      if (my_score > my_high_scores[i].score()) {
        my_high_scores[i] = the_new_high_score;
      }
    }
  }

  /**
   * A pair of a sequence of three initials and a score.
   *
   * @author Daire O'Doherty 06535691 (daireod@gmail.com)
   * @version 20 April 2008
   */
  public /*@ pure @*/ class HighScore implements HighScoreInterface {
/** size of the initials array.*/
    private final int my_array_size = 3;
    /**array to hold initials of player.*/
    private char[] my_name = new char[my_array_size];
    /** score of the player.*/
    private int my_current_score;

    //@ ensures 0 <= \result;
    public/*@ pure @*/ int score() {
      return my_current_score;
    }

    /**
     * @return What are your initials?
     */
    //@ ensures \results.length == 3;
    public/*@ pure \nonnullelements @*/ char[] initials() {
      return my_name;
    }

    /**
     * @param the_new_score This is your score.
     */
    //@ requires 0 <= the_new_score;
    //@ ensures score() == the_new_score;
    public void new_score(final int the_new_score) {
      my_current_score = the_new_score;
    }

    /**
     * @param the_new_initials These are your initials.
     */
    //@ requires the_new_intials.length == 3;
    //@ ensures initials().equals(\old(the_new_initials));
    public void new_initials(/*@ non_null @*/final char[] the_new_initials) {
      my_name = the_new_initials;
    }
  }
}

