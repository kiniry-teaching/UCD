package thrust.physics;

/**
 * @author 'keith.madden@ucdconnect.ie'.
 * @version '08-04-08'.
 */
public class Physic implements Physics {
  /**
   * Speed of Spaceship.
   */
  double my_speed;
  /**
   * Given direction of Spaceship.
   */
  double my_direction;
  /**
   * Gravitational Constant of Earth.
   */
  double my_gravitational_constant = 9.8;
  /**
   * Mass of Spaceship.
   */
  double my_mass;
  /**
   * Orientation of Spaceship in radian circle.
   */
  double my_orientation;
  /**
   * Position of Spaceship on an X, Y Graph.
   */
  double my_position;
  /**
   * Variable X in Position Graph.
   */
  double my_x;
  /**
   *  Variable Y in Position Graph.
   */
  double my_y;

  public double[] acceleration()
  {
    final double[] acceleration = {my_speed, my_direction};
    return acceleration;
  }

  /**
   * @return What is the gravitational constant?
   */
  public /*@ pure @*/ double gravitational_constant()
  {
    return my_gravitational_constant;
  }

  /**
   * @return What is your mass in kilograms?
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ double mass()
  {
    return my_mass;
  }

  /**
   * @return What is your momentum in kilograms*meters per second?
   */
  public /*@ pure @*/ double momentum()
  {
    final double momentum = my_mass * my_speed;
    return momentum;
  }

  /**
   * @return What is your orientation in radians?
   */
  public /*@ pure @*/ double orientation()
  {
    return my_orientation;
  }

  /**
   * @return What is your position in meters from the origin?
   */
  //@ ensures \result.length == 2;
  public /*@ pure @*/ double[] position()
  {
    final double[] position = {my_x, my_y};
    return position;
  }

  /**
   * @return What is your velocity in meters per second?
   */
  public /*@ pure @*/ double[] velocity()
  {
    final double[] velocity = {my_speed, my_direction};
    return velocity;
  }
}

