/**
 * Computing the behaviour of entities according to physical
 * simulation in two dimensions.
 * @author Patrick Nevin: 06754155:
 *         Robert Plunkett: 06038883:
 * @version 8 April 2008
 * @revised 20 April 2008
 */
package thrust.physics;
/**
 * @author Patrick Nevin (patrick.nevin@ucdconnect.ie)
 * @version 20 April 2008
 */
public class  PhysicsClass implements Physics {
  /**accelartion of an entity.*/
  //private double[] my_accelartion; (never used
  /**constant force,
   * On a screen top left corner has position (0,0), hence g reversed.
   **/
  private static final double GRAVITATIONAL_CONSTANT = 9.8;
  /**the mass of an entity in kg's.*/
  private double my_mass;
  /**the momentum of an entity giving by mass*velocity.*/
  //private double my_momentum;
  /**the angle of the direction of an entity giving in rad's.*/
  private double my_orientation;
  /**set of x,y co-ordinates, bearing in mind top left corner is the origin.*/
  //private double[] my_position;
  /**the speed of an entity  m/s in a giving direction.*/
  //private double[] my_velocity;
  /**the weight of an entity giving in kg's.*/
  private double my_weight;
  /**the speed of an entity in m/s.*/
  private double my_speed;
  /** The current y location of this entity.*/
  private double my_xPos;
  /** The current y location of this entity.*/
  private double my_yPos;
  /**The time in seconds that the entity has existed.*/
  private double my_time;
  /**
   * Create an instance of Physics an set the following attributes.
   * @param mass, set the Entities mass
   * @param x initial location of this entity
   * @param y location of this entity
   */
  public PhysicsClass(final double a_mass, final double a_x, final double a_y) {
    this.my_mass = a_mass;
    this.my_xPos = a_x;
    this.my_yPos = a_y;
  }
  /**
   * @return What is your acceleration in meters per second squared?
   */
  //@ ensures \result.length == 2;
  /*@ pure @*/
  public double[] acceleration() {
    final double[] acc = {this.my_speed, this.my_time};
    return acc;
  }
  /**
   * @return What is the gravitational constant?
   */
  public /*@ pure @*/ double gravitational_constant() {
    return GRAVITATIONAL_CONSTANT;
  }
  /**
   *Set entities mass in kg's?
   *@param entityMass set the Entities mass
   */
  //@ ensures 0 <= \result;
  public final void setMass(final double a_mass) {
    this.my_mass = a_mass;
  }
  /**
   * @return What is your mass in kg's?
   */
  //@ ensures 0 <= \result
  public /*@ pure @*/  double mass() {
    return this.my_mass;
  }
  /**
   * @return What is your momentum in kg's*meters per second?
   */
  public /*@ pure @*/ double momentum() {
    return (this.my_speed * this.my_weight);
  }
  /**
   * @return What is your orientation in rad's?
   */
  public /*@ pure @*/ double orientation() {
    return this.my_orientation;
  }
  /**
   * @return What is your position in meters from the origin?
   */
  //@ ensures \result.length == 2;
  public /*@ pure @*/ double[] position() {
    final double[] pos = {this.my_xPos, this.my_yPos};
    return pos;
  }

  /**
   * @return What is your velocity in meters per second?
   */
  public /*@ pure @*/ double[] velocity() {
    final double[] s = {this.my_speed, this.my_orientation};
    return s;
  }

}
