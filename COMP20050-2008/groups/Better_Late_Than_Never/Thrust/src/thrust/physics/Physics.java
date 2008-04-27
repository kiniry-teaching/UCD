package thrust.physics;

/** Class implementation of the PhysicsInterface.
 * @author Nicholas McCarthy (nicholas.mccarthy@gmail.com)
 * @version 27 April 2008
 */
public class Physics implements PhysicsInterface {

  /** Array holding acceleration and orientation of Entity. */
  private double[] my_acceleration;
  /** Double holding the gravitational constant value. */
  private final double my_gravitational_constant = 0;
  /** Double holding current mass of the ship. */
  private double my_mass;
  /** Double holding current momentum of the Entity. */
  private double my_momentum;
  /** Double holding orientation of ship in radians. */
  private double my_orientation;
  /** Array of doubles holding X and Y coordinates of Entity. */
  private double[] my_position;
  /** Array of doubles holding velocity and orientation of Entity. */
  private double[] my_velocity;
  /** Int for use in my_acceleration, my_position and my_velocity arrays. */
  private final int my_arraylength = 2;
  /** Double holding amount of seconds to simulate for. */
  private double my_seconds;

  /** Returns current acceleration of the Entity. */
  public double[] acceleration() {
    return my_acceleration;
  }

/** Returns the gravitational constant in use. */
  public double gravitational_constant() {
    return my_gravitational_constant;
  }

  /** Returns current mass of the Entity in kilograms. */
  public double mass() {
    return my_mass;
  }

/** Returns momentum of the Entity in kilograms*meters per second. */
  public double momentum() {
 // Assuming my_velocity[0] is current speed
    my_momentum = my_mass * my_velocity[0];
    return my_momentum;
  }

/** Returns orientation of the Entity in radians. */
  public double orientation() {
    return my_orientation;
  }

/** Returns position in metres from the origin of the Entity. */
  public double[] position() {
    return my_position;
  }

  // See: void velocity(the_velocity) method.
  // Changed from double[] to double here and in PhysicsInterface.
/** Returns current velocity of the Entity in metres per second. */
  public double velocity() {
    return my_velocity[0];
  }

  /** Calculates new acceleration of Entity. */
  public void acceleration(final double[] the_acceleration) {

    // If statement using my_arraylength because it equals 2
    // and 2 is a magic number.
    if (the_acceleration.length == my_arraylength) {
      my_acceleration = new double[my_arraylength];
      my_acceleration[0] = the_acceleration[0];
      my_acceleration[1] = the_acceleration[1];
    } else {
      System.out.print("the_acceleration.length must equal 2");
    }
  }

  /** Ensures mass is positive, equal to the_mass. */
  public void mass(final double the_mass) {

    if (the_mass < 0) {
      System.out.print("Mass cannot be negative.");
    } else {
      my_mass = the_mass;
    }
  }

/** Ensures orientatian is equal to the_orientation. */
  public void orientation(final double the_orientation) {

    my_orientation = the_orientation;
  }

/** Ensures positions match up, the_position.length must equal 2. */
  public void position(final double[] the_position) {

    if (the_position.length == my_arraylength) {
      my_position = new double[my_arraylength];
      my_position[0] = the_position[0];
      my_position[1] = the_position[1];
    } else {
      System.out.print("the_position.length must equal 2");
    }
  }

  // Assuming the_velocity[0] == current speed
  // and the_velocity[1] == current orientation
/** Ensures velocities match up, the_velocity.length must equal 2. */
  public void velocity(final double[] the_velocity) {

    if (the_velocity.length == my_arraylength) {
      my_velocity = new double[my_arraylength];
      my_velocity[0] = the_velocity[0];
      my_velocity[1] = the_velocity[1];
    } else {
      System.out.print("the_velocity.length must equal 2");
    }
  }

  public void simulate(final double some_seconds) {

    my_seconds = some_seconds;
  }

}
