package thrust.physics;


/**
 * Physics
 * @author Sean Jago 06588557
 * @revised Sean Jago, Naomi O' Reilly
 * @version 16 April '08
 */

public class Physics implements PhysicsInterface
 {
  /** Gravity, the force that pulls the ship down towards the land. */
  static final double my_gravity = -9.8;
  
  /** Speed, the Speed at which an Entity is traveling at. */
  double my_speed;

  /** Change In Speed, the rate of the change in speed of an Entity. */
  double my_speed_change;

  /** Mass, a dimensionless quantity representing the amount of matter in an Entity. */
  double my_mass;

  /** Momentum, product of mass and velocity of an Entity. */
  double my_momentum;

  /** Orientation, the direction of an entity. */
  double my_orientation;
 
  /** X-Coordinate, the x-coordinate where the enitity is placed. */
  double my_xco;

  /** Y-Coordinate, the y-coordinate where the entity is placed. */
  double my_yco;

  

  /**
  * @return What is your acceleration in meters per second squared?
  */
  public double[] acceleration()
  {
    double[] acceleration = {my_speed, my_speed_change};
    return acceleration;
  }

  /**
  * @return What is the gravitational constant?
  */
  public double my_gravitational_constant() 
  {
    return my_gravity;
  }

  /**
   * @return What is your orientation in radians?
   */
  public double orientation() 
  {
    return my_orientation;
  }

 /**
   * @return What is your mass in kilograms?
   */
   public double mass()
   {
     return my_mass;
   }

 /**
   * @return What is your momentum in kilogrammes*meters per second?
   */
  public double momentum() 
   {
    return my_mass * my_speed;
   } 

 /**
   * @return What is your position in meters from the origin?
   */
  public double[] position() 
  {
    final double[] position = {my_xco, my_yco};
    return position;
  }

 /**
   * @return What is your velocity in meters per second?
   */
  public double[] velocity() 
  {
    final double[] velocity = {my_speed, my_orientation};
    return velocity;
  }

}
