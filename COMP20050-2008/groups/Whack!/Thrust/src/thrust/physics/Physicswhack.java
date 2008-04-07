package thrust.physics;

public class Physicswhack implements Physics{
//@ constraint (* The gravitational constant never changes. *);
  //@ constraint gravitational_constant() == \old(gravitational_constant());

  /**
   * @return What is your acceleration in meters per second squared?
   */
  //@ ensures \result.length == 2;
  /*@ pure @*/public double[] acceleration(){
   
  }

  /**
   * @return What is the gravitational constant?
   */
  /*@ pure @*/ public double gravitational_constant(){
   return gravitational_constant;
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
  double whack_orientation;
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
  double whack_speed;
  double[] whack_velocity = {whack_orientation/whack_speed};
  /*@ pure @*/public double[] velocity(){
    //speed and direction
    
    return whack_velocity;
  }

}
