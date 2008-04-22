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
import java.util.Collection;

import thrust.animation.Animatable;
import thrust.animation.Animation;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;

/**
 * The vacuum in which entities exist.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Space extends StaticEntity
  implements NeutralEntity, Animatable {
  /**
   * @return What are your stars?"
   */
  public /*@ pure @*/ Collection stars() {
    assert false; //@ assert false;
    return null;
  }

  /**
   * Add this star to space.
   * @param the_star the star to add.
   */
  public void add_star(Star the_star) {
    assert false; //@ assert false;
  }

  public double[] acceleration() {
    // TODO Auto-generated method stub
    return null;
  }

  public double mass() {
    // TODO Auto-generated method stub
    return 0;
  }

  public double momentum() {
    // TODO Auto-generated method stub
    return 0;
  }

  public double[] velocity() {
    // TODO Auto-generated method stub
    return null;
  }

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

  public void animate() {
    // TODO Auto-generated method stub
    
  }

  public Animation animation() {
    // TODO Auto-generated method stub
    return null;
  }

  public void animation(Animation the_animation) {
    // TODO Auto-generated method stub
    
  }

  public double gravitational_constant() {
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

  public Color color() {
    // TODO Auto-generated method stub
    return null;
  }

  public void color(Color the_color) {
    // TODO Auto-generated method stub
    
  }

  //@ public invariant (* Terrain and space are disjoint. *);
}
