package thrust.entities.about;

/**
 * Stores current values of parameters of games's state.
 * @author Magdalena Zieniewicz (mazienie@gmail.com)
 * @version 24 April 2008
 * */
public class AbstractGameStateClass {

  /**
   * There are eight high scores.
   */
  public static final int HIGH_SCORE_COUNT = 8;
  //@ invariant HIGH_SCORE_COUNT == 8;
  //@ invariant (* There are eight high scores. *);
  private int my_bonus;
  private int my_current_fuel;
  private int my_maximum_fuel;
  private int my_score;
  private byte my_lives;
  private HighScoreInterface[] my_HighScores;

  /**
   * @return What is the current bonus?
   * @bon BONUS What is your value?
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ int bonus(){
    return my_bonus;
  }

  /**
   * @param the_new_value This is your new value.
   */
  //@ requires 0 <= the_new_value;
  //@ ensures bonus() == the_new_value;
  public void new_bonus(int the_new_value){
    my_bonus = the_new_value;
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
  public  /*@ pure @*/ int current_fuel(){
    return my_current_fuel;
  }

  /**
   * @return How much fuel can you contain?
   * @idea The maximum fuel of the spaceship.
   */
  //@ ensures 0 <= \result;
  public  /*@ pure @*/ int maximum_fuel(){
    return my_maximum_fuel;
  }

  /**
   * @return What is the current score?
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ int score(){
    return my_score;
  }

  //@ invariant (* Score is always non-negative and finite. *);
  //@ invariant 0 <= score();

  /**
   * Change the current score by this many points.
   * @param some_new_points the new points to add to the current score.
   */
  //@ ensures score() == \old(score() + some_new_points);
  public void change_score(int some_new_points){
    int a_new_score = score() + some_new_points;
    my_score = a_new_score;
  }

  /**
   * @return How many lives do you have?
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ byte lives(){
    return my_lives;
  }

  //@ invariant (* Number of lives is always non-negative and finite. *);
  //@ invariant 0 <= lives();

  /**
   * @param some_new_lives Change the current lives by this many lives.
   */
  //@ ensures lives() == \old(lives() + some_new_lives);
  public /*@ pure @*/ void change_lives(byte some_new_lives){
    byte new_lives = (byte) (lives() + some_new_lives);
    my_lives = new_lives;
  }

  /**
   * @return What are the current high scores?
   */
  //@ ensures \result.length == HIGH_SCORE_COUNT;
  //@ ensures \nonnullelements(\result);
  public/*@ pure @*/ HighScoreInterface[] high_scores(){
    my_HighScores = new HighScoreClass[HIGH_SCORE_COUNT];
    
   
    return my_HighScores;
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
  public /*@ pure non_null @*/
  HighScoreInterface high_score(int the_index){
    
    return my_HighScores[the_index];
    
  }

  /**
   *
   * @param the_high_score the potential high score to check.
   * @return Is this score a new high score?
   */
  /*@ ensures \result <==> high_scores()[0].score() >= the_high_score.score() &
    @                      the_high_score.score() >= high_scores()[HIGH_SCORE_COUNT-1].score();
    @*/
  public  /*@ pure @*/
  boolean new_high_score(/*@ non_null @*/ HighScoreInterface the_high_score){
    
    int j;
    for(j=0; j< HIGH_SCORE_COUNT; j++){ // find
    
      if(the_high_score.score() > my_HighScores[j].score())
        return true;
        
      else if(the_high_score.score() == my_HighScores[j].score() && j != (HIGH_SCORE_COUNT - 1)){
        return true;
      }
  }
    return false;
  }

  /**
   * @param the_new_high_score Insert this score into the high score table.
   */
  /*@ ensures new_high_score(the_new_high_score) ==>
    @         (\exists int i; 0 <= i & i < HIGH_SCORE_COUNT;
    @          high_score(i).equals(the_new_high_score));
    @*/
  
    public void add_high_score(/*@ non_null @*/ HighScoreInterface the_new_high_score){
  

    int i;
      for(i=0; 1< HIGH_SCORE_COUNT; i++) 
      
        if(the_new_high_score.score() > my_HighScores[i].score()){
          
          for(int k = i; k < HIGH_SCORE_COUNT-1; k++){
            my_HighScores[k] = my_HighScores[k+1];
          }
          my_HighScores[i] = the_new_high_score;
          }
          
        else if(the_new_high_score.score() == my_HighScores[i].score() && i != (HIGH_SCORE_COUNT - 1)){
          
          for(int k = i+ 1; k < HIGH_SCORE_COUNT-1; k++){
            my_HighScores[k] = my_HighScores[k+1];
          }
      
          my_HighScores[i+1] = the_new_high_score;
  
        }
    }
    
    
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
  
  
  /**
   * An implemantation of the HighScoreInterface.
   *
   * @author Magdalena Zieniewicz (mazienie@gmail.com)
   * @version 25 April 2008
   */
public class HighScoreClass implements HighScoreInterface{
    
    private char[] my_initials; 
    private  int my_score;

    
    public HighScoreClass(){
      my_score = 0;
      my_initials = new char[3];
    }
    
    /**
     * @return What is your score?
     */
    //@ ensures 0 <= \result;
    public /*@ pure @*/ int score(){
      return my_score;
    }

    /**
     * @return What are your initials?
     */
    //@ ensures \result.length == 3;
   public /*@ pure @*/ char[] initials(){
      return my_initials;
    }

    /**
     * @param the_new_score This is your score.
     */
    //@ requires 0 <= the_new_score;
    //@ ensures score() == the_new_score;
    public void new_score(int the_new_score){
      my_score = the_new_score;
    }

    /**
     * @param the_new_initials These are your initials.
     */
    //@ requires the_new_initials.length == 3;
    //@ ensures initials().equals(\old(the_new_initials));
    public void new_initials(/*@ non_null @*/ char[] the_new_initials){
      my_initials = the_new_initials;
    }

    //@ invariant (* High scores are always non-negative and finite. *);
    //@ invariant 0 <= score();

    //@ invariant (* Initials are always three characters in length. *);
    //@ invariant initials().length == 3;
  }
  
  
  
  
}
