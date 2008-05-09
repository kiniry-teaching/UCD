package thrust.physics;

/**
 * Implementing the behavior of entities according to physical
 * simulation in two dimensions.
 * @author Ursula Redmond (ursula.redmond@ucdconnect.ie)
 * @version 8 April 2008
 */
public class Physics {
  /**
   * The gravitational constant.
   */
  private static final double GRAV_CONST = 0.0000000000667300;

  /**
   * The spaceship's mass.
   */
  private static final double SPACESHIP_MASS = 50000;

//@ constraint (* The gravitational constant never changes. *);
  //@ constraint gravitational_constant() == \old(gravitational_constant());

  /**
   * @return What is your acceleration in meters per second squared?
   */
  //@ ensures \result.length == 2;
  public /*@ pure @*/ double[] acceleration()
  {
    return null;
  }

  /**
   * @return What is the gravitational constant?
   */
  public /*@ pure @*/ double gravitational_constant()
  {
    return GRAV_CONST;
  }

  /**
   * @return What is your mass in kilograms?
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ double mass()
  {
    return SPACESHIP_MASS;
  }

  /**
   * @return What is your momentum in kilograms*meters per second?
   */
  public /*@ pure @*/ double momentum()
  {
    return 0;
  }

  /**
   * @return What is your orientation in radians?
   */
  public /*@ pure @*/ double orientation()
  {
    return 0;
  }

  /**
   * @return What is your position in meters from the origin?
   */
  //@ ensures \result.length == 2;
  public /*@ pure @*/ double[] position()
  {
    return null;
  }

  /**
   * @return What is your velocity in meters per second?
   */
  public /*@ pure @*/ double[] velocity()
  {
    return null;
  }

}
