/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.entities;

import thrust.physics.PhysicsInterface;

/**
 * Entities whose position or orientation change.
 * @author Keith Byrne, Eoghan O'Donovan, Sean Russell (Jar@timbyr.com).
 * @version 18 April 2008
 */
public abstract class DynamicEntity extends Entity implements PhysicsInterface {
  /** Is the entity turning left? */
  private static boolean turnleft;
  /** IS the entity turning right? */
  private static boolean turnright;
  /** Is the entity thrusting? */
  private static boolean thrusting;
  /** Turn step. */
  private static final double TURN = Math.PI / 10;
  /** Thrust. */
  private static final double THRUST = 10;
  /** Acceleration of the entity. */
  private transient double[] my_acceleration;
  /** Gravitational constant. */
  private transient double my_gravConstant;
  /** The mass of the entity. */
  private transient double my_mass;
  /** The velocity of the entity. */
  private transient double[] my_velocity;
  /** The position of the entity. */
  private transient double[] my_position;
  /** The orientation of the entity in radians. */
  private transient double my_orientation;


  /**
   * @param the_position the initial position.
   * @param the_orientation the initial orientation.
   * @param the_acceleration the initial acceleration.
   * @param the_grav_constant the initial gravitational constant.
   * @param the_mass the initial mass.
   * @param the_velocity the initial velocity.
   */
  public void set_dynamic_state(final double[] the_position,
                                final double the_orientation,
                                final double[] the_acceleration,
                                final double the_grav_constant,
                                final double the_mass,
                                final double[] the_velocity) {
    my_position = new double[]{the_position[0], the_position[1]};
    my_orientation = the_orientation;
    my_acceleration = (double[])the_acceleration.clone();
    my_gravConstant = the_grav_constant;
    my_mass = the_mass;
    my_velocity = (double[])the_velocity.clone();
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#acceleration()
   */
  public double[] acceleration() {
    return (double[])my_acceleration.clone();
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#acceleration(double[])
   */
  public void acceleration(final double[] the_acceleration) {
    my_acceleration = (double[])the_acceleration.clone();
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#gravitational_constant()
   */
  public double gravitational_constant() {
    return my_gravConstant;
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#mass()
   */
  public double mass() {
    return my_mass;
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#mass(double)
   */
  public void mass(final double the_mass) {
    my_mass = the_mass;
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#momentum()
   */
  public double momentum() {
    return (my_mass * Math.hypot(my_velocity[0], my_velocity[1]));
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#orientation()
   */
  public double orientation() {
    return my_orientation;
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#orientation(double)
   */
  public void orientation(final double the_orientation) {
    my_orientation = the_orientation;
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#position()
   */
  public double[] position() {
    return new double[] {my_position[0], my_position[1] };
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#position(double[])
   */
  public void position(final double[] the_position) {
    my_position = (double[])the_position.clone();
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#simulate(double)
   */
  public void simulate(final double some_seconds) {
    for (int i = 0; i < some_seconds; i++) {
      if (thrusting) {
        my_acceleration[0] += THRUST * Math.cos(orientation());
        my_acceleration[1] += THRUST * Math.sin(orientation());
      }
      if (turnleft) {
        my_orientation += TURN;
      }
      if (turnright) {
        my_orientation -= TURN;
      }
      my_position[0] += my_velocity[0];
      my_position[1] += my_velocity[1];
      my_velocity[0] += my_acceleration[0];
      my_velocity[1] += my_acceleration[1];
      my_acceleration[1] += my_gravConstant;
    }
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#velocity()
   */
  public double[] velocity() {
    return (double[])my_velocity.clone();
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#velocity(double[])
   */
  public void velocity(final double[] the_velocity) {
    my_velocity = (double[])the_velocity.clone();
  }

  /**
   *
   * @param the_state
   */
  public void set_turnleft(final boolean the_state) {
    turnleft = the_state;
  }

   /**
    *
    * @param the_state
    */
  public void set_turnright(final boolean the_state) {
    turnright = the_state;
  }

  /**
   *
   * @param the_state
   */
  public void set_thrust(final boolean the_state) {
    thrusting = the_state;
  }

}
