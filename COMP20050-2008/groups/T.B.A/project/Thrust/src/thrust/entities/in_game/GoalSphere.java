/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */
package thrust.entities.in_game;

import java.awt.Color;
import java.awt.Shape;

import thrust.entities.DynamicEntity;
import thrust.entities.NeutralEntity;
import thrust.entities.behaviors.Tow;

/**
 * The goal sphere that the spaceship needs to tow into
 * space away from the terrain to escape.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class GoalSphere extends DynamicEntity
  implements NeutralEntity, Tow {

  public void render() {
    // TODO Auto-generated method stub
    
  }

  public Shape shape() {
    // TODO Auto-generated method stub
    return null;
  }

  public void shape(Shape the_shape) {
    // TODO Auto-generated method stub
    
  }

  public String shape_name() {
    // TODO Auto-generated method stub
    return null;
  }

  public byte state() {
    // TODO Auto-generated method stub
    return 0;
  }

  public void state(byte the_state) {
    // TODO Auto-generated method stub
    
  }

  public void tow() {
    // TODO Auto-generated method stub
    
  }

  public boolean towed() {
    // TODO Auto-generated method stub
    return false;
  }

  public double[] acceleration() {
    // TODO Auto-generated method stub
    return null;
  }

  public double gravitational_constant() {
    // TODO Auto-generated method stub
    return 0;
  }

  public double mass() {
    // TODO Auto-generated method stub
    return 0;
  }

  public double momentum() {
    // TODO Auto-generated method stub
    return 0;
  }

  public double orientation() {
    // TODO Auto-generated method stub
    return 0;
  }

  public double[] position() {
    // TODO Auto-generated method stub
    return null;
  }

  public void simulate(double some_seconds) {
    // TODO Auto-generated method stub
    
  }

  public double[] velocity() {
    // TODO Auto-generated method stub
    return null;
  }

  public Color color() {
    // TODO Auto-generated method stub
    return null;
  }

  public void color(Color the_color) {
    // TODO Auto-generated method stub
    
  }
  /*@ public invariant (* The fuel pod is destroyed by a bullet. *);
    @ public invariant (* If the fuel pod is destroyed, the spaceship
    @                     is destroyed. *);
    @ public invariant (* The goal sphere is destroyed by the factory's
    @                     chimney, but not its sphere. *);
    @ public invariant (* The goal sphere is not affected by the gun turret. *);
    @ public invariant (* The goal sphere is not affected by the fuel pod. *);
    @ public invariant (* The goal sphere is not affected by space. *);
    @ public invariant (* The goal sphere is not affected by stars. *);
    @ public invariant (* The goal sphere is destroyed by the terrain. *);
    @ public invariant (* When rendered on the terrain, the goal sphere
    @                     sits on a pedestal. *);
    @ public invariant (* When being towed, the goal sphere is rendered
    @                     as a sphere. *);
    @ public invariant (* The shape of the goal sphere is always a circle. *);
    @ public invariant (* The color of the goal sphere is always green. *);
    @ public invariant color() == thrust.entities.properties.GameColor.GREEN;
    @*/
}
