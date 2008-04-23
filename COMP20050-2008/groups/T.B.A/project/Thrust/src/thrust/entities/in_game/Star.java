/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @ creation_date "March 2007"
 * @ last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */
package thrust.entities.in_game;

import java.awt.Color;
import java.awt.Shape;

import thrust.animation.Animatable;
import thrust.animation.Animation;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;

/**
 * A blinking star in space.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Star extends StaticEntity
  implements NeutralEntity, Animatable {
  /**
   * The mass of an object.
   */
  double my_mass;
  /**
   * The speed of an object.
   */
  double my_speed;
  /**
   * The angle of an object, in radians.
   */
  double my_angleRadians;
  /**
   * The position of an object.
   */
  double[] my_xyPosition;

  public double[] acceleration() {
    // TODO Auto-generated method stub
    return null;
  }

  public double mass() {
    return my_mass;
  }

  public double momentum() {
    final int numberOfElements = 2;
    double[] speed = new double[numberOfElements];
    speed = velocity();
    return mass() * speed[0];
  }

  public double[] velocity() {
    final int numberOfElements = 2;
    final double[] my_velocity = new double[numberOfElements];
    my_velocity[0] = my_speed;
    my_velocity[1] = orientation();
    return my_velocity;
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
    final double gravity = -9.81;
    return gravity;
  }
  
  public void getOrientation(final double an_angle)
  {
    my_angleRadians = an_angle;
  }

  public double orientation() {
    return my_angleRadians;
  }

  public double[] position() {
    return my_xyPosition;
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
  /*@ public invariant (* A star's location is in space. *);
    @ public invariant (* A star interacts with no other entities. *);
    @ public invariant (* Each star blinks irregularly. *);
    @ public invariant (* A star's shape is always a small square. *);
    @*/
}
