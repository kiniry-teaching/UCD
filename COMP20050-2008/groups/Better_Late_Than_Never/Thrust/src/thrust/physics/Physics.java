package thrust.physics;

/** Class implementation of the PhysicsInterface.
 * @author Nicholas McCarthy (nicholas.mccarthy@gmail.com)
 * @version 27 April 2008
 */
public class Physics implements PhysicsInterface {

  /** Double holding the gravitational constant value. */
  private static final double GRAV_CONSTANT = 0;
  /** String to clean up assertion error messages. */
  private static final String ASSERTIONERROR =
    "The parameter array length != 2";
  /** Int for use in my_acceleration, my_position and my_velocity arrays. */
  private static final int ARRAYLENGTH = 2;
  /** Array holding acceleration and orientation of Entity. */
  private transient double[] my_acceleration;
  /** Double holding current mass of the ship. */
  private transient double my_mass;
  /** Double holding current momentum of the Entity. */
  private transient double my_momentum;
  /** Double holding orientation of ship in radians. */
  private transient double my_orientation;
  /** Array of doubles holding X and Y coordinates of Entity. */
  private transient double[] my_position;
  /** Array of doubles holding velocity and orientation of Entity. */
  private transient double[] my_velocity;
  /** Double holding amount of seconds to simulate for. */
  private transient double my_seconds;


  /** Returns current acceleration of the Entity. */
  public double[] acceleration() {
    return my_acceleration;
  }

/** Returns the gravitational constant in use. */
  public double gravitational_constant() {
    return GRAV_CONSTANT;
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
  public double[] velocity() {
    return my_velocity;
  }

  /** Calculates new acceleration of Entity. */
  public void acceleration(final double[] the_acceleration) {
    assert the_acceleration.length == ARRAYLENGTH : ASSERTIONERROR;
    System.arraycopy(the_acceleration, 0, my_acceleration, 0,
                     the_acceleration.length);
  }

  /** Ensures mass is positive, equal to the_mass. */
  public void mass(final double the_mass) {

    assert the_mass >= 0;
    my_mass = the_mass;
  }

/** Ensures orientatian is equal to the_orientation. */
  public void orientation(final double the_orientation) {

    my_orientation = the_orientation;
  }

/** Ensures positions match up, the_position.length must equal 2. */
  public void position(final double[] the_position) {
    assert the_position.length == ARRAYLENGTH : ASSERTIONERROR;
    System.arraycopy(the_position, 0, my_position, 0, the_position.length);

  }

  // Assuming the_velocity[0] == current speed
  // and the_velocity[1] == current orientation
/** Ensures velocities match up, the_velocity.length must equal 2. */
  public void velocity(final double[] the_velocity) {
    assert the_velocity.length == ARRAYLENGTH : ASSERTIONERROR;
    System.arraycopy(the_velocity, 0, my_velocity, 0, the_velocity.length);
  }

  public void simulate(final double some_seconds) {

    my_seconds = some_seconds;
  }

}
