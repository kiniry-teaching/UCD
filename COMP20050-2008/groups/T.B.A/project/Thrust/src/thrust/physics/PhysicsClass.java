package thrust.physics;
/**
 * Computing the behavior of entities according to physical
 * simulation in two dimensions.
 * @author Dave Haughton (Dave.haughton1@gmail.com)
 * @version 2 April 2008
 */
public abstract class PhysicsClass {

/**
   * The angle of the ship.
   */
  double my_angleRadians;

  /**
   * The mass of an object.
   */
  double my_mass;

  /**
   * The position of an object.
   */
  double[] my_xyPosition;

  /**
   * The speed of an object.
   */
  double my_speed;


  abstract double[] acceleration();

  double gravitational_constant()
  {
    final double gravity = 9.81;
    return gravity;
  }

  public void setMass(final double some_mass)
  {
    my_mass = some_mass;
  }

  double mass()
  {
    return my_mass;
  }

  double momentum()
  {
    final int numberOfElements = 2;
    double[] speed = new double[numberOfElements];
    speed = velocity();
    return mass() * speed[0];
  }

  public void getOrientation(final double an_angle)
  {
    my_angleRadians = an_angle;
  }

  double orientation()
  {
    return my_angleRadians;
  }

  /**
   * @return the x and y coordinates of an object.
   */
  double[] position()
  {
    return my_xyPosition;
  }


  /**
   * @param takes an x coordinate and a y coordinate.
   */
  public void  getPosition(final double a_position_x, final double a_position_y)
  {
    final int xyCoordinate = 2;
    my_xyPosition = new double[xyCoordinate];
    my_xyPosition[0] = a_position_x;
    my_xyPosition[1] = a_position_y;
  }

  /**
   * @param takes a speed.
   */
  public void setSpeed(final double a_speed)
  {
    my_speed = a_speed;
  }

  /**
   * @return the velocity of an object (i.e. the speed and direction).
   */
  public double[] velocity()
  {
    final int numberOfElements = 2;
    final double[] my_velocity = new double[numberOfElements];
    my_velocity[0] = my_speed;
    my_velocity[1] = orientation();
    return my_velocity;
  }
}
