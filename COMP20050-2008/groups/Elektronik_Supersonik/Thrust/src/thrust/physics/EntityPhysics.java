package thrust.physics;

/**
 * @author Dominic Carr (dominiccarr@gmail.com)
 * @version 8 April 2008
 * This class implements Physics
 */
public class EntityPhysics implements Physics {
  /**
   * The gravitational constant.
   */
  private final double my_grav_constant;

  //@ constraint (* The gravitational constant never changes. *);
  //@ constraint gravitational_constant() == \old(gravitational_constant());

  /**
   * @return What is your acceleration in meters per second squared?
   */
  //@ ensures \result.length == 2;
  public/*@ pure @*/double[] acceleration() {
  }

  /**
   * @return What is the gravitational constant?
   */
  public /*@ pure @*/double gravitational_constant() {
    return my_grav_constant;
  }

  /**
   * @return What is your mass in kilograms?
   */
  //@ ensures 0 <= \result;
  public/*@ pure @*/double mass() {
  }

  /**
   * @return What is your momentum in kilograms*meters per second?
   */
  public/*@ pure @*/double momentum() {
  }

  /**
   * @return What is your orientation in radians?
   */
  public/*@ pure @*/double orientation() {
  }

  /**
   * @return What is your position in meters from the origin?
   */
  //@ ensures \result.length == 2;
  public/*@ pure @*/double[] position() {
  }

  /**
   * @return What is your velocity in meters per second?
   */
  public/*@ pure @*/double[] velocity() {
  }
}
