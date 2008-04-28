package thrust.entities.about;

/**
 * *This class is for the highscore interface.
 * @author David Haughton (dave.haughton1@gmail.com)
 * @version 28 April 2008
 */
public class HighScore  implements  AbstractGameState.HighScoreInterface {
  /**
   * stores the current score.
   */
  int my_score;

  /**
   * stores the initials of the player.
   */
  char[] my_initials;
     /**
      * @return What is your score?
      */
     //@ ensures 0 <= \result;
     /*@ pure @*/
  public int score()
  {
    return my_score;
  }
     /**
      * @return What are your initials?
      */
     //@ ensures \results.length == 3;
     /*@ pure \nonnullelements @*/

  public char[] initials()
  {
    return my_initials;
  }

     /**
      * @param the_new_score This is your score.
      */
     //@ requires 0 <= the_new_score;
     //@ ensures score() == the_new_score;
  public void new_score(final int the_new_score)
  {
    this.my_score = the_new_score;
  }

     /**
      * @param the_new_initials These are your initials.
      */
     //@ requires the_new_intials.length == 3;
     //@ ensures initials().equals(\old(the_new_initials));
  public  void new_initials(/*@ non_null @*/final char[] the_new_initials)
  {
    this.my_initials = the_new_initials;
  }


}
