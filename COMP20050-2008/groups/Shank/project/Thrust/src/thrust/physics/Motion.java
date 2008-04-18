package thrust.physics;

/**
 * Implementing the physics interface.
 * @author KevinLambe kevinlamb@hotmail.com
 * @version 7 April 2008
 * edited 8 April 2008
 */
public abstract class Motion implements Physics
{
  //Creating all the double variables required
  /**Put javadoc comments in please.*/
  private double accel;
  /**Put javadoc comments in please.*/
  private double[] acc;
  /**Put javadoc comments in please.*/
  private double[] vel;
  /**Put javadoc comments in please.*/
  private double[] pos;
  /**Put javadoc comments in please.*/
  private double mass;
  /**Put javadoc comments in please.*/
  private double moment;
  /**Put javadoc comments in please.*/
  private double radian;
  /**Put javadoc comments in please.*/
  private double velocity;
  public void acceleration(final double vel, final double time)
  {
   /*
    * calculating acceleration
    * acceleration = change in velocity with respect to time(velocity/time)
    *
    *calculates magnitude of acceleration and direction
    */
    final int accCoordinates = 2;
    acc = new double[accCoordinates];
    accel = vel / time;
    acc[0] = accel;
    acc[1] = orientation();
  }
  public double[] acceleration()
  {
    return  acc;
  }
  public double gravitational_constant()
  {
    final double g = 9.81;
    return g; //returns g, gravitational constant
  }
  public double mass()
  {
    //returns mass of entity
    return mass;
  }
  public void momentum(final double mass, final double vel)
  {
    //calculating momentum
    //momentum = mass * velocity
    moment = mass * vel;
  }
  public double momentum()
  {
    //returns momentum
    return moment;
  }
  public double orientation()
  {
    //returns orientation of the entity
    return radian;
  }
  public void myPosition(final double myXPos, final double myYPos)
  {
    final int size = 2;
    pos = new double[size];
    pos[0] = myXPos;
    pos[1] = myYPos;
  }
  public double[] position()
  {
  //returns position in meters
    return pos;
  }
  public void myVelocity(final double p1, final double p2, final double t)
  {
    /*Change in position with respect to time
    *p2-p1/time
    *calculates direction and magnitude of velocity
    */
    velocity = (p2 - p1) / t;
    final int size = 2;
    vel = new double[size];
    vel[0] = velocity;
    vel[1] = orientation();
  }
  public double[] velocity()
  {
    //returns velocity in meters per second
    return vel;
  }
}
