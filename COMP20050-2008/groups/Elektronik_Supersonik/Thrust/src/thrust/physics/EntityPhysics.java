package thrust.physics;

/**
 * This class implements Physics.
 * @author Dominic Carr (dominiccarr@gmail.com)
 * @version 8 April 2008
 */
public class EntityPhysics implements Physics {
  /**
   * The gravitational constant.
   */
  private static final double GRAV_CONST = 0.0000000000667300;
  /**
   * The Mass.
   */
  private transient double my_mass;
  /**
   * The speed.
   */
  private transient double my_speed;
  /**
   * the orientation.
   */
  private transient double my_orientation;
  /**
   * the weight.
   */
  private transient double my_weight;
  /**
   * the velocity.
   */
  private transient double[] my_velocity = {0, 0};
  /**
   * the position.
   */
  private transient double[] my_position = {0, 0};
  /**
   * the acceleration.
   */
  private transient double[] my_acceleration = {0, 0};

  //@ constraint (* The gravitational constant never changes. *);
  //@ constraint gravitational_constant() == \old(gravitational_constant());

  /**
   * @return What is your acceleration in meters per second squared?
   */
  //@also ensures \result.length == 2;
  public/*@ pure @*/double[] acceleration() {
    return new double[] {my_acceleration[0], my_acceleration[1]};
  }

  /**
   * @return What is the gravitational constant?
   */
  public /*@ pure @*/double gravitational_constant() {
    return GRAV_CONST;
  }

  /**
   * @return What is your mass in kilograms?
   */
  //@also ensures 0 <= \result;
  public/*@ pure @*/double mass() {
    double ret = 0;
    if (my_mass >= 0) {
      ret = my_mass;
    }
    return ret;
  }

  /**
   * @return What is your momentum in kilograms*meters per second?
   */
  public/*@ pure @*/double momentum() {
    return my_speed * my_weight;
  }

  /**
   * @return What is your orientation in radians?
   */
  public/*@ pure @*/double orientation() {
    return my_orientation;
  }

  /**
   * @return What is your position in meters from the origin?
   */
  //@also ensures \result.length == 2;
  public/*@ pure @*/double[] position() {
    return new double[] {my_position[0], my_position[1]};
  }

  /**
   * @return What is your velocity in meters per second?
   */
  public/*@ pure @*/double[] velocity() {
    return new double[] {my_velocity[0], my_velocity[1]};
  }
}
