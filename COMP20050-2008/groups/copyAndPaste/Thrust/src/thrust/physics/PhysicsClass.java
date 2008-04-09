package thrust.physics;

/**
 * Computing the behaviour of entities according to physical
 * simulation in two dimensions.
 * @author Patrick Nevin: 06754155:
 *         Robert Plunkett: 06038883:
 * @version 8 April 2008
 */
 
/**
 * Sorry I've never done physics so having difficulty determining
 * what these concept actually do, so finding it hard to provide
 * an implementation who's functionality i don't know....
 */
public class  PhysicsClass implements Physics {
  /**accelartion of an entity.*/
  private double[] accelartion;
  /**constant force,
   * On a screen top left corner has position (0,0), hence g reversed.
   **/
  private static final double gravitational_constant = 9.8;
  /**the mass of an entity in kg's.*/
  private double mass;
  /**the momentum of an entity giving by mass*velocity.*/
  private double momentum;
  /**the angle of the direction of an entity giving in rad's.*/
  private double orientation;
  /**set of x,y co-ordinates, bearing in mind top left corner is the origin.*/
  private double[] position;
  /**the speed of an entity giving in meters per second.*/
  private double[] velocity;
  /** The current y location of this entity.*/
  private double xPos;
  /** The current y location of this entity */
  private double yPos;
  /** The current speed of this entity horizontally (pixels/seconds).*/
  private double dx;
  /** The current speed of this entity vertically (pixels/seconds).*/
  private double dy;
  
  /**
   * Create an instance of Physics an set the following attributes.
   * 
   * @param mass, set the Entities mass
   * @param x initial location of this entity
   * @param y location of this entity
   */
  public PhysicsClass(double mass,double x,double y) {
    this.mass = mass;
    this.xPos = x;
    this.yPos = y;
  }
  

  /**
   * @return What is your acceleration in meters per second squared?
   */
  //@ ensures \result.length == 2;
  /*@ pure @*/
  public double[] acceleration() {
    return null;
    
  }

  /**
   * @return What is the gravitational constant?
   */
  
  public /*@ pure @*/ double gravitational_constant() {
    return gravitational_constant;
  }
  /**
   *Set entities mass in kg's?
   * @param entityMass set the Entities mass 
   */
  //@ ensures 0 <= \result;
  public final void setMass(final double entityMass) {
    this.mass = entityMass;
  }
  /**
   * @return What is your mass in kg's?
   */
  //@ ensures 0 <= \result
  public /*@ pure @*/  double mass() {
    return this.mass;
  }
  /**
   * @return What is your momentum in kg's*meters per second?
   */
  
  public /*@ pure @*/ double momentum() {
    return this.momentum;
  }
  
  /**
   * @return What is your orientation in rad's?
   */
  public /*@ pure @*/ double orientation() {
    return this.orientation;
  }
  
  /**
   * @return What is your position in meters from the origin?
   */
  //@ ensures \result.length == 2;
  
  public /*@ pure @*/ double[] position() {
    final double[] pos = {this.xPos, this.yPos};
    return pos;
  }

  /**
   * @return What is your velocity in meters per second?
   */
   public /*@ pure @*/ double[] velocity() {
    final double[] s = {this.dx, this.dy};
    return s;
  }

}
