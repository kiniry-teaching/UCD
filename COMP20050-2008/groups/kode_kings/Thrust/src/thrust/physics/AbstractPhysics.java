package thrust.physics;

/**
 * Implementation of Physics methods.
 * @author Colin Casey (colin.casey.2@gmail.com)
 * @version 7 April 2008
 */
public abstract class AbstractPhysics implements Physics {
  /** The force that attracts the spaceship and
   * goal sphere toward the terrain. */
  final double my_gravity_constant = -9.8;
  /** The quantity of matter that an entity contains. */
  double my_mass;
  /** The rate of motion. */
  double my_speed;
  /** Change in the speed of something. */
  double my_rate_of_speed;
  /** The relative physical direction of entities. */
  double my_orientation;
  /** The x co-ordinate where an entity is located. */
  double my_position_x;
  /** The y co-ordinate where an entity is located. */
  double my_position_y;

  public double[] acceleration() {
    final double[] acceleration = {my_speed, my_rate_of_speed};
    return acceleration;
  }

  public double gravitational_constant() {
    return my_gravity_constant;
  }

  public double mass() {
    return my_mass;
  }

  public double momentum() {
    return my_mass * my_speed;
  }

  public double orientation() {
    return my_orientation;
  }

  public double[] position() {
    final double[] position = {my_position_x, my_position_y};
    return position;
  }

  public double[] velocity() {
    final double[] velocity = {my_speed, my_orientation};
    return velocity;
  }

}
