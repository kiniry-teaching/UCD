package thrust.physics;

/**
 * implementing the Physics interface.
 */
/**
 * @author Tara Flood (Tara.Flood@ucdconnect.ie)
 * @version 8 April 2008
 */

public class Physicswhack implements PhysicsInterface {

  /**
   * Variable X in Position.
   */
  double my_x;
  /**
   *  Variable Y in Position.
   */
  double my_y;
  /**
   * implementing double speed.
   */
  double my_whackspeed;
  /**
   * implementing double Orientation.
   */
  double my_whackorientation;
  /**
   * impementing mass.
   */
  double my_whackmass;
  /**
   * @return What is your acceleration in meters per second squared?
   */

  //@ ensures \result.length == 2;
  double[] my_whackacceleration = {my_whackspeed, my_whackorientation};
  /*@ pure @*/public double[] acceleration() {
    //size and direction
    return my_whackacceleration;
  }

  /**
   * @return What is the gravitational constant?
   */
  /*@ pure @*/ public double gravitational_constant() {
    return GRAVITATIONAL_CONSTANT;
  }

  /**
   * @return What is your mass in kilograms?
   */

  //@ ensures 0 <= \result;
  /*@ pure @*/public double mass() {
    return my_whackmass;
  }


  /**
   * @return What is your momentum in kilograms*meters per second?
   */
  /*@ pure @*/public double momentum() {
    return (mass() * my_whackspeed);
  }

  /**
   * @return What is your orientation in radians?
   */

  /*@ pure @*/ public double orientation() {
    return my_whackorientation;

  }

  /**
   * @return What is your position in meters from the origin?
   */

  //@ ensures \result.length == 2;
  /*@ pure @*/public double[] position() {
    final double[] position = {my_x, my_y};
    return position;
  }

  /**
   * @return What is your velocity in meters per second?
   */


  /*@ pure @*/public double[] velocity() {
    //speed and direction
    final double[] my_whackvelocity = {my_whackspeed, my_whackorientation};
    return my_whackvelocity;
  }
  /**
   * @param a_time_interval the amount of time that has passed.
   */
  public void simulate(final double a_time_interval) {
  }
  /**
   * @param the_acceleration This is your acceleration.
   */
  //@ requires the_acceleration.length == 2;
  //@ ensures acceleration()[0] == the_acceleration[0];
  //@ ensures acceleration()[1] == the_acceleration[1];
  public void acceleration(final double[] the_acceleration) {
    // TODO Auto-generated method stub

  }

  /**
   * @param the_mass This is your mass.
   */
  //@ requires 0 <= the_mass;
  //@ ensures mass() == the_mass;
  public void mass(final double the_mass) {
    // TODO Auto-generated method stub

  }

  /**
   * @param the_orientation This is your orientation.
   */
  //@ ensures orientation() == the_orientation;
  public void orientation(final double the_orientation) {
    // TODO Auto-generated method stub

  }
  /**
   * @param the_position This is your position.
   */
  //@ requires the_position.length == 2;
  //@ ensures position()[0] == the_position[0];
  //@ ensures position()[1] == the_position[1];
  public void position(final double[] the_position) {
    // TODO Auto-generated method stub

  }
  /**
   * @param the_velocity This is your velocity.
   */
  //@ requires the_velocity.length == 2;
  //@ ensures velocity()[0] == the_velocity[0];
  //@ ensures velocity()[1] == the_velocity[1];
  public void velocity(final double[] the_velocity) {
    // TODO Auto-generated method stub

  }

}
