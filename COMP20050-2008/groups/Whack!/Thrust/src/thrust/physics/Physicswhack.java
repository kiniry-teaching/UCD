package thrust.physics;

/**
 * implementing the Physics interface.
 */
/**
 * @author Tara Flood (Tara.Flood@ucdconnect.ie)
 * @version 8 April 2008
 */

public class Physicswhack implements Physics {
/**
 * implementing double speed.
 */
  double whack_speed;
  /**
   * implementing double Orientation.
   */
  double whack_orientation;
  /**
   * @return What is your acceleration in meters per second squared?
   */
  //@ ensures \result.length == 2;
  double[] whack_acceleration = {whack_speed * whack_orientation};
  /*@ pure @*/public double[] acceleration() {
    //size and direction
    return whack_acceleration;
  }

  /**
   * @return What is the gravitational constant?
   */
  /*@ pure @*/ public double gravitational_constant(){
    return whack_gravitational_constant;
  }

  /**
   * @return What is your mass in kilograms?
   */
  double whack_mass;
  //@ ensures 0 <= \result;
  /*@ pure @*/public double mass(){
    return whack_mass;
  }


  /**
   * @return What is your momentum in kilograms*meters per second?
   */
  /*@ pure @*/public double momentum(){
    return whack_mass*(whack_speed*whack_orientation);
  }

  /**
   * @return What is your orientation in radians?
   */

  /*@ pure @*/ public double orientation(){
    return whack_orientation;

  }

  /**
   * @return What is your position in meters from the origin?
   */
  double x;
  double y;
  //@ ensures \result.length == 2;
  /*@ pure @*/public double[] position(){
    final double[] whack_position = {x, y};
    return whack_position;
  }

  /**
   * @return What is your velocity in meters per second?
   */

  double[] whack_velocity = {whack_orientation/whack_speed};
  /*@ pure @*/public double[] velocity(){
    //speed and direction

    return whack_velocity;
  }

}
