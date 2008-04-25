package thrust.physics;

/**
 * Implementing the physics interface.
 * @author Kevin Lambe (kwlambe@hotmail.com)
 * @version 7 April 2008
 * edited 18 April 2008 by Roger Thomas & Kevin Lambe
 */
public abstract class Motion implements PhysicsInterface
{
  //Creating all the double variables required
  /**
   * double field.
   * acceleration of ship
   */
  private double my_accel;
  /**
   * Array of doubles.
   * holds my_accel and orientation
   */
  private double[] my_acc;
  /**
   * double field.
   * Sets the speed of the ship
   */
  private double my_speed;
  /**
   * Array of doubles.
   * Holds speed and orientation
   */
  private double[] my_vel;
  /**
   * Array of doubles.
   * holds x position and y position
   */
  private double[] my_pos;
  /**
   * Double field.
   * holds the mass of the ship
   */
  private double my_mass;
  /**
   * Double field.
   * Holds momentum of ship
   */
  private double my_moment;
  /**
   * Double field.
   * Holds the angle of the orientation of the ship
   */
  private double my_radian;
  /**Put info here.*/
  public void acceleration(final double the_vel, final double the_time)
  {
   /*
    * calculating acceleration
    * acceleration = change in velocity with respect to time(velocity/time)
    *
    *calculates magnitude of acceleration and direction
    */
    final int accCoordinates = 2;
    my_acc = new double[accCoordinates];
    my_accel = the_vel / the_time;
    my_acc[0] = my_accel;
    my_acc[1] = orientation();
  }
  /**Put info here.*/
  public double[] acceleration()
  {
    return  my_acc;
  }
  /**Put info here.*/
  public double gravitational_constant()
  {
    final double g = 9.81;
    return g; //returns g, gravitational constant
  }
  /**Put info here.*/
  public double mass()
  {
    //returns mass of entity
    return my_mass;
  }
  /**Put info here.*/
  public void momentum(final double the_mass, final double the_vel)
  {
    //calculating momentum
    //momentum = mass * velocity
    my_moment = the_mass * the_vel;
  }
  /**Put info here.*/
  public double momentum()
  {
    //returns momentum
    return my_moment;
  }
  /**Put info here.*/
  public double orientation()
  {
    //returns orientation of the entity
    return my_radian;
  }
  /**Put info here.*/
  public void myPosition(final double the_xpos, final double the_ypos)
  {
    final int size = 2;
    my_pos = new double[size];
    my_pos[0] = the_xpos;
    my_pos[1] = the_ypos;
  }
  /**Put info here.*/
  public double[] position()
  {
  //returns position in meters
    return my_pos;
  }
  /**Put info here.*/
  public void setSpeed(final double a_speed)
  {
    my_speed = a_speed;
  }
  /**Put info here.*/
  public void myVelocity()
  {
    /*
     * Change in position with respect to time
     *calculates direction and magnitude of velocity
     */
    final int size = 2;
    my_vel = new double[size];
    my_vel[0] = my_speed;
    my_vel[1] = orientation();
  }
  /**Put info here.*/
  public double[] velocity()
  {
    //returns velocity in meters per second
    return my_vel;
  }
}
