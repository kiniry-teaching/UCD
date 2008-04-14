package thrust.physics;

/**
 * @author keith.madden@ucdconnect.ie
 * @version 08-04-08.
 */
public class K_Physic implements Physics {
  /**
   * Speed of Spaceship.
   */
double my_speed;
/**
 * Given direction of Spaceship.
*/
double my_direction;

double my_gravitational_constant = 9.8;
double my_mass;
double my_orientation;
double my_position;
double my_x;
double my_y;

  public double[] acceleration()
  {
    final double[] acceleration = {K_speed, K_direction};
    return acceleration;
  }

  /** 
   * @return What is the gravitational constant? 
   */ 
  public /*@ pure @*/ double gravitational_constant()
  {
    return K_gravitational_constant;
  }

  /** 
   * @return What is your mass in kilograms? 
   */ 
  //@ ensures 0 <= \result; 
  public /*@ pure @*/ double mass()
  {
    return K_mass;
  }

  /** 
   * @return What is your momentum in kilograms*meters per second? 
   */ 
  public /*@ pure @*/ double momentum()
  {
    double momentum = K_mass*K_speed;
    return momentum;
  }
  
     /** 
    * @return What is your orientation in radians? 
    */ 
     public /*@ pure @*/ double orientation()
     {
      return K_orientation;
     }
    
     /** 
    * @return What is your position in meters from the origin? 
    */ 
     //@ ensures \result.length == 2; 
     public /*@ pure @*/ double[] position()
     {
       final double[] position = {K_x, K_y};
      return position;
     }
    
     /** 
    * @return What is your velocity in meters per second? 
    */ 
     public /*@ pure @*/ double[] velocity()
     {
       final double[] velocity = {K_speed, K_direction};
      return velocity;
     }
}

