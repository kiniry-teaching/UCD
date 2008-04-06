package thrust.physics;

public interface Physics {
  //@ constraint (* The gravitational constant never changes. *);
  //@ constraint G() == \old(G());

  /**
   * @return What is your acceleration in meters per second squared?
   */
  //@ ensures \result.length == 2;
  public /*@ pure @*/ double[] acceleration();

  /**
   * @return What is the gravatational constant?
   */
  public /*@ pure @*/ double G();

  /**
   * @return What is your mass in kilograms?
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ double mass();

  /**
   * @return What is your momentum in kilograms*meters per second?
   */
  public /*@ pure @*/ double momentum();

  /**
   * @return What is your orientation in radians?
   */
  public /*@ pure @*/ double orientation();

  /**
   * @return What is your position in meters from the origin?
   */
  //@ ensures \result.length == 2;
  public /*@ pure @*/ double[] position();

  /**
   * @return What is your velocity in meters per second?
   */
  public /*@ pure @*/ double[] velocity();
}
