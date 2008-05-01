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

/**
 * The state of the Thrust game, including current score, bonus, fuel, lives,
 * and high scores.
 *
 * @author simo markey (kiniry@acm.org)
 * @version 11 April 2008
 */
public class GameState extends FuelAble{
  public GameState(float initialFuel) {
    super(initialFuel);
    
    int my_bonus;
    byte my_lives;
    int my_fuel;
    int maximum_fuel;
    boolean death=false;
    
    int HighScoreInterface[] my_highScores;
    
    int my_HIGH_SCORE_COUNT= 8;
    // TODO Auto-generated constructor stub
  }

  //static int bonus=0;
  //static int lives=4;
  
  //int score=0;
  //static int my_bonus=0;
  
  /**
   * There are eight high scores.
   */
  
 // HIGH_SCORE_COUNT =8;
  //@ invariant HIGH_SCORE_COUNT ==8;
  //@ invariant (* There are eight high scores. *);

  /**
   * @return What is the current bonus?
   * @bon BONUS What is your value?
   */
  //@ ensures 0 <= \result;
  public static /*@ pure @*/ int bonus() {
    
    return my_bonus;
  }

  /**
   * @param the_new_value This is your new value.
   */
  //@ requires 0 <= the_new_value;
  //@ ensures bonus() == the_new_value;
  public void new_bonus(int the_new_value) {
    the_new_value =0;
    bonus= the_new_value;
    
    if(my_bonus<0)
     my_bonus= 0;
    //should really be bonus = bonus^2-bonus^2; which gives 0
    else
    {my_bonus= my_bonus*1;}
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
  public /*@ pure @*/ float current_fuel() {
    return Fuel;
  }

  /**
   * @return How much fuel can you contain?
   * @idea The maximum fuel of the spaceship.
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ float maximum_fuel() {
    //return Float.POSITIVE_INFINITY;
    return maximum_fuel();
  }

  /**
   * @return What is the current score?
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ int score() {
    int my_score =0;
    if(my_score<0)
      my_score=0;
    return my_score;
   
  }
 
  //@ invariant (* Score is always non-negative and finite. *);
  //@ invariant 0 <= score();

  /**
   * Change the current score by this many points.
   * @param some_new_points the new points to add to the current score.
   */
  //@ ensures score() == \old(score() + some_new_points);
  public void change_score(int some_new_points) {
    score = score()+some_new_points;
   
    
  }

  /**
   * @return How many lives do you have?
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ byte lives() {
    lives =4;
    return (byte) lives;
  }
  
  
  //@ invariant (* Number of lives is always non-negative and finite. *);
  //@ invariant 0 <= lives();

  /**
   * @param some_new_lives Change the current lives by this many lives.
   */
  //@ ensures lives() == \old(lives() + some_new_lives);
  public /*@ pure @*/ void change_lives(byte some_new_lives) {
    some_new_lives =1;
    if(!death)
    (lives) = lives+some_new_lives;
    else
      (lives)= lives - some_new_lives;
  }

  /**
   * @return What are the current high scores?
   */
  //@ ensures \result.length == HIGH_SCORE_COUNT;
  //@ ensures \nonnullelements(\result);
  public /*@ pure @*/ HighScoreInterface[] high_scores() {
    //high_scores =HIGH_SCORE_COUNT;
    return null;
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
  public /*@ pure non_null @*/HighScoreInterface high_score() {
    int j;
    for(j=0;j < HIGH_SCORE_COUNT;j++)
    {}
    for(int i=HIGH_SCORE_COUNT;i>j; i--)
    { 
      //WTF WARHFHGHGGH
     if (high_scores()[i].score() >= high_scores()[j].score())
     {
       int tempScore = high_scores()[i].score();
       high_scores()[i].new_score(high_scores()[j].score());
       high_scores()[j].new_score(tempScore);
       
     }
    }
    

    return null;
  }

  /**
   *
   * @param the_high_score the potential high score to check.
   * @return Is this score a new high score?
   */
  /*@ ensures \result <==> high_scores()[0].score() >= the_high_score.score() &
    @                      the_high_score.score() >= high_scores()[HIGH_SCORE_COUNT-1].score();
    @*/
  public /*@ pure @*/
  boolean new_high_score(/*@ non_null @*/ HighScoreInterface the_high_score) {
    return false;
  }

  /**
   * @param the_new_high_score Insert this score into the high score table.
   */
  /*@ ensures new_high_score(the_new_high_score) ==>
    @         (\exists int i; 0 <= i & i < HIGH_SCORE_COUNT;
    @          high_score(i).equals(the_new_high_score));
    @*/
  public void
  add_high_score(/*@ non_null @*/ HighScoreInterface the_new_high_score) {
    for(int i=0;i>=0&&i<HIGH_SCORE_COUNT;i++)
    {high_score(i).equals(the_new_high_score);}
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
}
