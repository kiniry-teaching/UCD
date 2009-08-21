/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.entities;

import java.awt.Color;

import thrust.physics.PhysicsInterface;

/**
 * Entities whose position or orientation change.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public abstract class DynamicEntity extends Entity
  implements PhysicsInterface {

  public double[] acceleration() {
    // TODO Auto-generated method stub
    return null;
  }

  public void acceleration(double[] the_acceleration) {
    // TODO Auto-generated method stub
    
  }

  public double gravitational_constant() {
    // TODO Auto-generated method stub
    return 0;
  }

  public double mass() {
    // TODO Auto-generated method stub
    return 0;
  }

  public void mass(double the_mass) {
    // TODO Auto-generated method stub
    
  }

  public double momentum() {
    // TODO Auto-generated method stub
    return 0;
  }

  public double orientation() {
    // TODO Auto-generated method stub
    return 0;
  }

  public void orientation(double the_orientation) {
    // TODO Auto-generated method stub
    
  }

  public double[] position() {
    // TODO Auto-generated method stub
    return null;
  }

  public void position(double[] the_position) {
    // TODO Auto-generated method stub
    
  }

  public void simulate(double some_seconds) {
    // TODO Auto-generated method stub
    
  }

  public double[] velocity() {
    // TODO Auto-generated method stub
    return null;
  }

  public void velocity(double[] the_velocity) {
    // TODO Auto-generated method stub
    
  }

  public Color color() {
    // TODO Auto-generated method stub
    return null;
  }

  public void color(Color the_color) {
    // TODO Auto-generated method stub
    
  }
}
