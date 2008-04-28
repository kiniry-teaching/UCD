package thrust.entities.about;

public class HighScore implements HighScoreInterface
{
    /**
     * @return What is your score?
     */
    public //@ ensures 0 <= \result;
    /*@ pure @*/ int score() {
      return 0;
    }

    /**
     * @return What are your initials?
     */
    public //@ ensures \result.length == 3;
    /*@ pure @*/ char[] initials() {
      //THIS IS DODGY
      char[] sig = new char[3];
      if(sig.length>3)
      {break;}
      return sig;
    }

    /**
     * @param the_new_score This is your score.
     */
    public //@ requires 0 <= the_new_score;
    //@ ensures score() == the_new_score;
    void new_score(int the_new_score) {
      the_new_score = score();
    }

    /**
     * @param the_new_initials These are your initials.
     */
    public //@ requires the_new_initials.length == 3;
    //@ ensures initials().equals(\old(the_new_initials));
    void new_initials(/*@ non_null @*/ char[] the_new_initials) {
      //i dont know change the array? huhrh doggie WTF BBQ CAKE WIN NO PANTS DANCE
      
    }

    //@ invariant (* High scores are always non-negative and finite. *);
    //@ invariant 0 <= score();

    //@ invariant (* Initials are always three characters in length. *);
    //@ invariant initials().length == 3;
  }
}
