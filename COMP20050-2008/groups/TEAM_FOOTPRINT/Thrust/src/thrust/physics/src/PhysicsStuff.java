
//class written by Daire O'Doherty 06535691 3/4/08
public class PhysicsStuff {
		
	
	//@ constraint (* The gravitational constant never changes. *);
	  //@ constraint gravitational_constant() == \old(gravitational_constant());
	
	  /**
	   * @return What is your acceleration in meters per second squared?
	   */
	  //@ ensures \result.length == 2;
	  /*@ pure @*/ double acceleration(double x,double y){
		  //acceleration = difference in V/difference in time, metre/second squared
		  return x % y;
	  }
	
	  /**
	   * @return What is the gravitational constant?
	   */
	  /*@ pure @*/public double gravity(){
		  double vgravity = 9.81; //earth gravity is 9.81 metres per second squared
		  
		  return vgravity;
	  }
	
	  
	  /**
	   * @return What is your mass in kilograms?
	   */
	  //@ ensures 0 <= \result;
	  /*@ pure @*/ double mass = 10;
	
	  /**
	   * @return What is your momentum in kilograms*meters per second?
	   */
	  /*@ pure @*/ double momentum(double m, double v){
		  
		   m = mass;
		   v= velocity;
		  
		  return m*v ;
	  }
	
	  /**
	   * @return What is your orientation in radians?
	   */
	  /*@ pure @*/ double orientation(){
		  return 0; 
	  }
	
	  /**
	   * @return What is your position in meters from the origin?
	   */
	  //@ ensures \result.length == 2;
	  /*@ pure @*/ double[] position(){
		  //x+y coordinate
		  return null;
	  }
	
	  /**
	   * @return What is your velocity in meters per second?
	   */
	  /*@ pure @*/ double[] velocity (double p1,double p2,double t){
		  //change in position versus time
		  //position 2 - position1%time
		  return p1-p2 % t;
		  
		  
	  }
	
	

}
