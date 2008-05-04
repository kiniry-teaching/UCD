package thrust.physics;

/**
 * Implementing the behavior of entities according to physical
 * simulation in two dimensions.
 * @author Ursula Redmond (ursula.redmond@ucdconnect.ie)
 * @version 8 April 2008
 */
public class DynamicEntity {

  /**
   * mass of spaceship.
   */
  private transient double my_mass;

  /**
   * gravitational constant.
   */
  private transient double my_gravity;

//@ constraint (* The gravitational constant never changes. *);
  //@ constraint gravitational_constant() == \old(gravitational_constant());

  /**
   * @return What is your acceleration in meters per second squared?
   */
  //@ ensures \result.length == 2;
  public /*@ pure @*/ double[] acceleration()
  {
    return null;
  }

  public void setmass(final double the_mass)
  {
    my_mass = the_mass;
  }

  public void setgravity(final double the_grav)
  {
    my_gravity = the_grav;
  }

  /**
   * @return What is the gravitational constant?
   */
  public /*@ pure @*/ double gravitational_constant()
  {
    return my_gravity;
  }

  /**
   * @return What is your mass in kilograms?
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ double mass()
  {
    return my_mass;
  }

  /**
   * @return What is your momentum in kilograms*meters per second?
   */
  public /*@ pure @*/ double momentum()
  {
    final double m = mass();
    final double[] v = velocity();
    final double x = v[0] * m;
    final double y = v[1] * m;
    return Math.sqrt((x * x) + (y * y));
  }

  /**
   * @return What is your orientation in radians?
   */
  public /*@ pure @*/ double orientation()
  {
    final double mone = 0;
    final double[] a = position();
    final double half = 2;
    final double mtwo = (a[1] - a[0]) / (a[1] / half - a[0] / half);
    final double tantheta = Math.abs((mone - mtwo) / (1 + (mone * mtwo)));
    return Math.atan(tantheta);
  }

  /**
   * @return What is your position in meters from the origin?
   */
  //@ ensures \result.length == 2;
  public /*@ pure @*/ double[] position()
  {
    return null;
  }

  /**
   * @return What is your velocity in meters per second?
   */
  public /*@ pure @*/ double[] velocity()
  {
    return null;
  }

}
