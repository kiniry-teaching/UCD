/* A re-implementation of the classic C=64 game 'Thrust'.
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */
package thrust.entities;
import thrust.physics.PhysicsClass;
/**
 * Entities whose position or orientation change.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 * @revised patrick nevin (patrick.nevin@ucdconnect.ie)
 */
public abstract class DynamicEntity extends Entity {
  /**
   * create an instance of physics to wrap behaviour around.
   */
  private PhysicsClass my_physics = new PhysicsClass();
  /**
   * Set the position and orientation of this entity.
   * @param the_position the position.
   * @param the_orientation the orientation.
   */
  //@ ensures position()[0] == the_position[0];
  //@ ensures position()[1] == the_position[1];
  //@ ensures orientation() == the_orientation;
  public void set_state(final double[] the_pos, final double the_ori) {
    my_physics.position(the_pos);
    my_physics.orientation(the_ori);
  }
  /**
   * @return the mass of the object.
   */
  public double mass() {
    return my_physics.mass();
  }
  /**
   * @param the_mass of the Entity
   */
  public void set_mass(final double the_mass) {
    my_physics.mass(the_mass);
  }
  /**
   * @return the Entities velocity.
   */
  public double[] velocity() {
    return my_physics.velocity();
  }
  /**
   * @param the_velocity the Entities velocity
   */
  public void set_velocity(final double[] the_velocity) {
    my_physics.velocity(the_velocity);
  }
  /**
   * @return the Entities acceleration
   */
  public double[] acceleration() {
    return my_physics.acceleration();
  }
  /**
   * @param the_acceleration
   */
  public void set_acceleration(final double[] the_acceleration) {
    my_physics.acceleration(the_acceleration);
  }
  /**
   * @return the Entities momentum.
   */
  public double momentum() {
    return my_physics.momentum();
  }
  /**
   * Simulate this object for some seconds.
   */
  public void simulate(final double some_seconds) {
    my_physics.simulate(some_seconds);
  }
}
