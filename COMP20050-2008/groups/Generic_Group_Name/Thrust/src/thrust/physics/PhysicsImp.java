package thrust.physics;
import java.util.*;
import java.io.*;

public PhysicsImp implements Physics {
  
  final double my_position_x=0;
  final double my_position_y=0;
  double vel_magnitude=0;
  double vel_direction=0;
  final double grav_constant=0.00000000006673;
  double m=0;
  //@ constraint (* The gravitational constant never changes. *);
  //@ constraint G() == \old(G());

  /**
   * @return What is your acceleration in meters per second squared?
   */
  //@ ensures \result.length == 2;
  public /*@ pure @*/ double[] acceleration() {
    	long startTime = System.currentTimeMillis() * 100;
    	double startVel = velocity();
    	long endTime = System.currentTimeMillis() * 100;
    	double endVel = velocity();
    
    	double changeVel = endVel - startVel;
    	long changeTime = endTime - startTime;
    
    	double acc = changeVel / changeTime;
    
    	return acc;
  }

  /**
   * @return What is the gravatational constant?
   */
  public /*@ pure @*/ double G() {
      return grav_constant;
  }

  /**
   * @return What is your mass in kilograms?
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ double mass() {
      return m;
  }

  /**
   * @return What is your momentum in kilograms*meters per second?
   */
  public /*@ pure @*/ double momentum() {
      return mass() * velocity().vel[0];
  }

  /**
   * @return What is your orientation in radians?
   */
  public /*@ pure @*/ double orientation();

  /**
   * @return What is your position in meters from the origin?
   */
  //@ ensures \result.length == 2;
  public /*@ pure @*/ double[] position() {
        final double[] position = new double[2];
        
        position[0] = my_position_x;
        position[1] = my_position_y;
        
        return position;
  }

  /**
   * @return What is your velocity in meters per second?
   */
  public /*@ pure @*/ double[] velocity() {
       double[] vel = new double[2];
             
       vel[0] = vel_magnitude;
       vel[1] = vel_direction;
       
       return vel;
  }


}
