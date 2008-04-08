package thrust.physics;

/**
 * Computing the behavior of entities according to physical
 * simulation in two dimensions.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public interface Physics {
  //@ constraint (* The gravitational constant never changes. *);
  //@ constraint gravitational_constant() == \old(gravitational_constant());

  /**
   * @return What is your acceleration in meters per second squared?
   */
  //@ ensures \result.length == 2;
  /*@ pure @*/ double[] acceleration();

  /**
   * @return What is the gravitational constant?
   * @return Will return the gravitional constant of 9.8 m/s
   */
  /*@ pure @*/ double gravitational_constant(){
    return double 9.8;
  }

  /**
   * @return What is your mass in kilograms?
   */
  //@ ensures 0 <= \result;
  /*@ pure @*/ double mass(){
    return mass;
  }

  /**
   * @return What is your momentum in kilograms*meters per second?
   */
  /*@ pure @*/ double momentum();

  /**
   * @return What is your orientation in radians?
   */
  /*@ pure @*/ double orientation();

  /**
   * @return What is your position in meters from the origin?
   */
  //@ ensures \result.length == 2;
  /*@ pure @*/ double[] position(){
    double orig_X = get_X; //have when the key press for move forward is pressed
    double orig_Y = get_Y; // to record the orginal X/Y position and then when the key press is over to get the new current X/Y
    
    double current_X = get_X;
    double current_Y = get_Y;
    testing
    
    double Displaced_X;
    double Displaced_Y;
  }

  /**
   * @return What is your velocity in meters per second?
   */
  /*@ pure @*/ double[] velocity();
}
