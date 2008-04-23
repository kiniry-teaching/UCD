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
  /** Increase in the rate of speed of something. */
  private static double[] my_acceleration;
  /** The quantity of matter that an entity contains. */
  private static double my_mass;
  /** The quantity of motion of a moving entity. */
  private static double my_momentum;
  /** The speed of an entity in a given direction. */
  private static double[] my_velocity;
  /** The relative physical direction of entities. */
  private static double my_orientation;
  /** The co-ordinates where an entity is located. */
  private static double[] my_position;;

  public double[] acceleration() {
    return my_acceleration;
  }

  public double gravitational_constant() {
    return GRAVITY_CONSTANT;
  }

  public double mass() {
    return my_mass;
  }

  public double momentum() {
    return my_momentum;
  }

  public double orientation() {
    return my_orientation;
  }

  public double[] position() {
    return my_position;
  }

  public double[] velocity() {
    return my_velocity;
  }

  public void position(final double[] the_position) {
    my_position = the_position;
  }

  public void orientation(final double the_orientation) {
    my_orientation = the_orientation;
  }

  public void mass(final double the_mass) {
    my_mass = the_mass;
  }

  public void velocity(final double[] the_velocity) {
    my_velocity = the_velocity;
  }

  public void acceleration(final double[] the_acceleration) {
    my_acceleration = the_acceleration;
  }

  public void simulate(final double some_seconds) {

  }
}
