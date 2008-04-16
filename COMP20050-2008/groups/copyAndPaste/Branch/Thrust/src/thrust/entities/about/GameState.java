package thrust.entities.about;

import thrust.entities.about.AbstractGameState.HighScoreInterface;

/**
 * The state of the Thrust game, including current score, bonus, fuel, lives,
 * and high scores.
 * Processes and delegates each keyboard input received.
 * @author Patrick Nevin: 06754155
 * @version 13 April 2008
 * 
 */
public class GameState extends AbstractGameState {
  
  private int bonus;
  private int fuel;
  private int max_fuel;
  private int current_score;
  private byte lives;
  public final HighScoreClass[] HIGH_SCORE_COUNTS;
  
  public GameState(int bonus, int fuel, int max_fuel, int score, byte lives) {
     this.bonus = bonus;
     this.fuel = fuel;
     this.max_fuel = max_fuel;
     this.current_score = score;
     this.lives = lives;
     this.HIGH_SCORE_COUNTS = new HighScoreClass[8];
  }
  /**
   * @return What is the current bonus?
   * @bon BONUS What is your value?
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ int bonus() {
      return this.bonus;
  }
  
  /**
   * @param the_new_value This is your new value.
   */
  //@ requires 0 <= the_new_value;
  //@ ensures bonus() == the_new_value;
  public void new_bonus(int the_new_value) {
      this.bonus = the_new_value;
  }
  
  /**
   * @return How much fuel do you contain?
   * @design The current fuel of the spaceship.
   * @note Note that the {@link Spaceship} class should be the 
   * actual owner of this data; this is just a convenience method.
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ int current_fuel() {
    return this.fuel;
  }

  /**
   * @return How much fuel can you contain?
   * @design The maximum fuel of the spaceship.
   */
  //@ ensures 0 <= \result;
  public  /*@ pure @*/ int maximum_fuel() {
     return this.max_fuel;
  }

  /**
   * @return What is the current score?
   */
  //@ ensures 0 <= \result;
  public  /*@ pure @*/ int score() {
    return this.current_score;
  }

  /**
   * Change the current score by this many points.
   * @param some_new_points the new points to add to the current score.
   */
  //@ ensures score() = \old(score() + some_new_points);
  public  void change_score(int some_new_points) {
     this.current_score += some_new_points;
  }

  /**
   * @return How many lives do you have?
   */
  //@ ensures 0 <= \result;
  public  /*@ pure @*/ byte lives() {
    return this.lives;
  }

  /**
   * @param some_new_lives Change the current lives by this many lives.
   */
  //@ ensures lives() == \old(lives() + some_new_lives);
  public  /*@ pure @*/ void change_lives(byte some_new_lives) {
    this.lives += some_new_lives;
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
  public  /*@ pure \nonnullelements @*/ HighScoreInterface[] high_scores() {
    return this.HIGH_SCORE_COUNTS;
  }

  public  /*@ pure non_null @*/ HighScoreInterface high_score(int the_index) {
    return this.HIGH_SCORE_COUNTS[the_index];
  }

  public  /*@ pure @*/ boolean new_high_score(/*@ non_null @*/ HighScoreInterface the_possible_new_high_score) {
    return (this.HIGH_SCORE_COUNTS[0].score == the_possible_new_high_score.score());
    
  }

  public  void add_high_score(/*@ non_null @*/ HighScoreInterface the_new_high_score) {
    for (int i = 0; i < 8; i++) {
      if (this.HIGH_SCORE_COUNTS[i].score <= the_new_high_score.score()) {
        this.HIGH_SCORE_COUNTS[i] = (HighScoreClass)the_new_high_score;
        
        
      }
    }
  }

  private class HighScoreClass implements HighScoreInterface {
    private char[] initialsArray = new char[3];
    private int score;
    
     
    /**
     * @return What is your score?
     */
    //@ ensures 0 <= \result;
    public /*@ pure @*/ int score() {
      return this.score;
    }

    /**
     * @return What are your initials?
     */
    //@ ensures \results.length == 3;
    public /*@ pure \non-null-elements @*/ char[] initials() {
       return this.initialsArray;
    }

    /**
     * @param the_new_score This is your score.
     */
    //@ requires 0 <= the_new_score;
    //@ ensures score() == the_new_score;
    public void new_score(int the_new_score) {
      this.score = the_new_score;
    }

    /**
     * @param the_new_initials These are your initials.
     */
    //@ requires the_new_intials.length == 3;
    //@ ensures initials().equals(\old(the_new_initials));
    public void new_initials(/*@ non_null @*/ char[] the_new_initials) {
      this.initialsArray = the_new_initials;
    }
    
  }
}
  