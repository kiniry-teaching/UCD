import thrust.entities.in_game.AbstractGameState.HighScoreInterface;

public class GameState implements AbstractGameState {
  int bonus=0;
  int fuel=0;
  int max_fuel=10000;
  int score=0;
  byte lives=0;
  final int HIGH_SCORE_COUNT = 8;
  HighScore[] high_scores = new HighScore[HIGH_SCORE_COUNT];
  HighScore the_current_high_score;

  public int bonus() {
    return bonus;
  }

  /**
   * @param the_new_value This is your new value.
   */
  //@ requires 0 <= the_new_value;
  //@ ensures bonus() == the_new_value;
  public void new_bonus(int the_new_value) {
    if(the_new_value > 0 || the_new_value == 0) {
        bonus = the_new_value;
    }    
  }

  /**
   * @return How much fuel do you contain?
   * @design The current fuel of the spaceship.
   * @note Note that the {@link Spaceship} class should be the 
   * actual owner of this data; this is just a convenience method.
   */
  //@ ensures 0 <= \result;
  public int current_fuel() {
    return fuel;
  }

  /**
   * @return How much fuel can you contain?
   * @design The maximum fuel of the spaceship.
   */
  //@ ensures 0 <= \result;
  public int maximum_fuel() {
    return max_fuel;
  }

  /**
   * @return What is the current score?
   */
  //@ ensures 0 <= \result;
  public int score() {
    return score;
  }

  /**
   * Change the current score by this many points.
   * @param some_new_points the new points to add to the current score.
   */
  //@ ensures score() = \old(score() + some_new_points);
  public void change_score(int some_new_points) {
    score = score + some_new_points;
  }

  /**
   * @return How many lives do you have?
   */
  //@ ensures 0 <= \result;
  public byte lives() {
    if(lives < 0) {
      //game ends
      System.out.println("YOU DIED!!! LOSER");
      return lives;
    }
    return lives;
  }

  /**
   * @param some_new_lives Change the current lives by this many lives.
   */
  //@ ensures lives() == \old(lives() + some_new_lives);
  public void change_lives(byte some_new_lives) {
    lives = (byte)(lives + some_new_lives);
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
  public HighScore[] high_scores() {
    
    //insertion sort
    int in, out;
    
    for(out=1; out > HIGH_SCORE_COUNT; out--) {
      int temp = high_scores[out].score;
      in = out;
      while(in > 0 && high_scores[in -1].score >= temp) {
        high_scores[in] = high_scores[in -1];
        --in;
      }
      high_scores[in].score = temp;
    }
    //end of insertion sort
    
    return high_scores;    
  }

  public HighScore high_score(int the_index) {
    return high_scores[the_index];
  }

  public boolean new_high_score(HighScore the_possible_new_high_score) {
    //sort the array
    high_scores();
    if(high_scores[0].score() == the_possible_new_high_score.score()){
      add_high_score(the_possible_new_high_score);
      return true;
    }
    return false;
  }

  public void add_high_score(HighScore the_new_high_score) {
    the_current_high_score = the_new_high_score;
  }

  /**
   * A pair of a sequence of three initials and a score.
   *
   * @author David McGinn
   * @author Michael Fahey
   * @author Cillian O'Neill
   * @version 25 April 2008
   */
  public class HighScore implements HighScoreInterface {
     int score=0;
     char[] initials = new char[3];
    /**
     * @return What is your score?
     */
    //@ ensures 0 <= \result;
    int score() {
      return score;
    }

    /**
     * @return What are your initials?
     */
    //@ ensures \results.length == 3;
   char[] initials() {
     return initials;
   }

    /**
     * @param the_new_score This is your score.
     */
    //@ requires 0 <= the_new_score;
    //@ ensures score() == the_new_score;
    void new_score(int the_new_score) {
      if (the_new_score > 0 || the_new_score == 0)
        score = the_new_score;
    }

    /**
     * @param the_new_initials These are your initials.
     */
    //@ requires the_new_intials.length == 3;
    //@ ensures initials().equals(\old(the_new_initials));
    void new_initials(char[] the_new_initials) {
      if (the_new_initials.length == 3) {
        initials = the_new_initials;
      }
    }
  }
}
