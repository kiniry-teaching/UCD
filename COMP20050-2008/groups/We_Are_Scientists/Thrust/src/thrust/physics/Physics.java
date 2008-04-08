package thrust.physics;

/**
 * Implementing the behavior of entities according to physical
 * simulation in two dimensions.
 * @author Ursula Redmond (ursula.redmond@ucdconnect.ie)
 * @version 8 April 2008
 */
public class Physics {
//@ constraint (* The gravitational constant never changes. *);
  //@ constraint gravitational_constant() == \old(gravitational_constant());

  /**
   * @return What is your acceleration in meters per second squared?
   */
  //@ ensures \result.length == 2;
  /*@ pure @*/ double[] acceleration()
  {
    return null;
  }

  /**
   * @return What is the gravitational constant?
   */
  /*@ pure @*/ double gravitational_constant()
  {
    final double gravity = 9.8;
    return gravity;
  }

  /**
   * @return What is your mass in kilograms?
   */
  //@ ensures 0 <= \result;
  /*@ pure @*/ double mass()
  {
    final double mass = 50000;
    return mass;
  }

  /**
   * @return What is your momentum in kilograms*meters per second?
   */
  /*@ pure @*/ double momentum()
  {
    return 0;
  }

  /**
   * @return What is your orientation in radians?
   */
  /*@ pure @*/ double orientation()
  {
    return 0;
  }

  /**
   * @return What is your position in meters from the origin?
   */
  //@ ensures \result.length == 2;
  /*@ pure @*/ double[] position()
  {
    return null;
  }

  /**
   * @return What is your velocity in meters per second?
   */
  /*@ pure @*/ double[] velocity()
  {
    return null;
  }

}
