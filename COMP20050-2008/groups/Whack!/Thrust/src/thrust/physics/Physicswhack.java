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
    
  }

  /**
   * @return What is your mass in kilograms?
   */
  //@ ensures 0 <= \result;
  /*@ pure @*/public double mass(){
    
  }

  /**
   * @return What is your momentum in kilograms*meters per second?
   */
  /*@ pure @*/public double momentum(){
    
  }
  /**
   * @return What is your orientation in radians?
   */
  /*@ pure @*/ public double orientation(){
    
  }

  /**
   * @return What is your position in meters from the origin?
   */
  //@ ensures \result.length == 2;
  /*@ pure @*/public double[] position(){
    
  }

  /**
   * @return What is your velocity in meters per second?
   */
  /*@ pure @*/public double[] velocity(){
    
  }

}
