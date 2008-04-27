package thrust.physics;

/** Class implementation of the PhysicsInterface.
 * @author Nicholas McCarthy (nicholas.mccarthy@gmail.com)
 * @version 27 April 2008
 */
public class Physics2 implements PhysicsInterface {

  /** Array holding acceleration and orientation of Entity. */
  private double[] my_acceleration;
  /** Double holding the gravitational constant value. */
  private double my_gravitational_constant;
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
  private static final int MY_ARRAYLENGTH = 2;



  /** Returns current acceleration of the Entity. */
  public double[] acceleration() {
    return my_acceleration;
  }
/** Returns the gravitational constant in use. */
  public double gravitational_constant() {
    my_gravitational_constant = 0;
    return my_gravitational_constant;
  }
  /** Returns current mass of the Entity in kilograms. */
  public double mass() {
    return my_mass;
  }
/** Returns momentum of the Entity in kilograms*meters per second. */
  public double momentum() {
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

/** Returns current velocity of the Entity in metres per second. */
  public double[] velocity() {
    return my_velocity;
  }


  /** Calculates new acceleration of Entity. */
  public void acceleration(double[] the_acceleration) {
 // All it says in the PhysicsInterface is that this method ensures 
 // my_acceleration == the_acceleration, but where does the_acceleration 
 // array come from, or does that come later?
    my_acceleration = new double[MY_ARRAYLENGTH];
    my_acceleration[0] = the_acceleration[0];
    my_acceleration[1] = the_acceleration[1];

  }

  /** Ensures mass is positive, equal to the_mass. */
  public void mass(double the_mass) {

  }

/** Ensures orientatian is equal to the_orientation. */
  public void orientation(double the_orientation) {
    // TODO Auto-generated method stub

  }

/** Ensures positions match up, the_position.length must equal 2. */
  public void position(double[] the_position) {
    // TODO Auto-generated method stub

  }

/** Ensures velocities match up, the_velocity.length must equal 2. */
  public void velocity(double[] the_velocity) {
    // TODO Auto-generated method stub

  }

  public void simulate(double some_seconds) {
    // TODO Auto-generated method stub

  }
}
