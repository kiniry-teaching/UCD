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
  double my_whackspeed;
  /**
   * implementing double Orientation.
   */
  double my_whackorientation;
  /**
   * @return What is your acceleration in meters per second squared?
   */
  //@ ensures \result.length == 2;
  double[] my_whackacceleration = {my_whackspeed * my_whackorientation};
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
    final double my_whackmass = 0;
    return my_whackmass;
  }


  /**
   * @return What is your momentum in kilograms*meters per second?
   */
  /*@ pure @*/public double momentum() {
    return mass() * (my_whackspeed * my_whackorientation);
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
    /** the x position. */
    final double my_x = 0;
   /** the y position. */
    final double my_y = 0;
    final double[] whack_position = {my_x, my_y};
    return whack_position;
  }

  /**
   * @return What is your velocity in meters per second?
   */


  /*@ pure @*/public double[] velocity() {
  //speed and direction
    final double[] my_whackvelocity = {my_whackspeed, my_whackorientation};
    return my_whackvelocity;
  }

}
