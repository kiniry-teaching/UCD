package thrust.physics;

/**
 * Implementation of Physics methods.
 * @author Colin Casey (colin.casey@org.com)
 * @version 7 April 2008
 */
public class KKPhysics implements PhysicsInterface {
  /** The force that attracts the spaceship and
   * goal sphere toward the terrain. */
  private static final double GRAVITY_CONSTANT = -9.8;
  /** The quantity of matter that an entity contains. */
  private static double my_mass;
  /** The rate of motion. */
  private static double my_speed;
  /** Change in the speed of something. */
  private static double my_rate_of_speed;
  /** Increase in the rate of speed of something. */
  private static double[] my_acceleration = {my_speed, my_rate_of_speed};
  /** The relative physical direction of entities. */
  private static double my_orientation;
  /** The x co-ordinate where an entity is located. */
  private static double my_position_x;
  /** The y co-ordinate where an entity is located. */
  private static double my_position_y;

  /**
   * @return What is your acceleration in meters per second squared?
   */
  public double[] acceleration() {
    return my_acceleration;
  }

  /**
   * @return What is the gravitational constant?
   */
  public double gravitational_constant() {
    return GRAVITY_CONSTANT;
  }

  /**
   * @return What is your mass in kilogrammes?
   */
  public double mass() {
    return my_mass;
  }

  /**
   * @return What is your momentum in kilogrammes*meters per second?
   */
  public double momentum() {
    return my_mass * my_speed;
  }

  /**
   * @return What is your orientation in radians?
   */
  public double orientation() {
    return my_orientation;
  }

  /**
   * @return What is your position in meters from the origin?
   */
  public double[] position() {
    final double[] position = {my_position_x, my_position_y};
    return position;
  }

  /**
   * @return What is your velocity in meters per second?
   */
  public double[] velocity() {
    final double[] velocity = {my_speed, my_orientation};
    return velocity;
  }

  public void simulate(final double some_seconds)
  {

  }
}
