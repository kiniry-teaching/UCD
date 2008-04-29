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
import com.sun.j3d.utils.geometry.Sphere;


/**
 * The goal sphere that the spaceship needs to tow into
 * space away from the terrain to escape.
 * @author Tara Flood (Tara.Flood@ucdconnect.ie)
 * @version 29 April 2008
 */
public class GoalSphere extends DynamicEntity implements NeutralEntity, Tow {
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
    @ public invariant color() == java.awt.Color.GREEN;
    @*/

  //@ public invariant (* The mass of the goal sphere is 10,000kg. *);
  /**
   * The mass of the goal sphere is 10,000kg.
   */
  public static final int MASS = 10000;
  /**
   * DynamicEntity.
   */
  DynamicEntity my_dynamicentity;
  /**
   * Velocity.
   */
  double[] my_velocity;
  /**
   * acceleration.
   */
  double[] my_acceleration;
  /**
   * sphere color.
   */
  Color my_spherecolor;
  /**
   * time.
   */
  double my_time;
  /**
   * position.
   */
  double [] my_position;
  /**
   * orientation.
   */
  double my_orientation;
  /**
   * mass.
   */
  double my_mass;
  /**
   * sphere.
   */
  Shape my_sphereshape;
  /**
   * radius.
   */
  float my_radius;
  /**
   * sphere.
   */
  Sphere my_sshape;
  public void tow() {
    // TODO Auto-generated method stub
  }

  public boolean towed() {
    // TODO Auto-generated method stub
    return false;
  }

  public double[] acceleration() {
    return my_acceleration;
  }

  public void acceleration(final double[] the_acceleration) {
    my_dynamicentity.acceleration();
  }

  public double gravitational_constant() {
    return my_dynamicentity.gravitational_constant();
  }

  public double mass() {
    my_mass = 1;
    return my_mass;
  }

  public void mass(final double the_mass) {
    my_dynamicentity.mass(the_mass);
  }


  public double momentum() {
    return my_dynamicentity.momentum();
  }

  public double orientation() {
    return my_orientation;
  }

  public void orientation(final double the_orientation) {
    my_dynamicentity.orientation(the_orientation);

  }
  public double[] position() {
    return  my_position;
  }

  public void position(final double[] the_position) {
    my_dynamicentity.position(the_position);
  }

  public void simulate(final double some_seconds) {
    my_time = some_seconds;
  }

  public double[] velocity() {
    return my_velocity;
  }

  public void velocity(final double[] the_velocity) {
    my_dynamicentity.velocity(the_velocity);
  }
  public Color color() {
    my_spherecolor.equals(Color.GREEN);
    return my_spherecolor;
  }

  public void color(final Color the_color) {
    my_spherecolor = the_color;
  }
  public void sphere(final float the_radius) {
    my_sshape.sphere(the_radius);
  }

  public Shape shape() {
    final sphere my_sphere = new sphere(1);

    my_sphereshape = (Shape)my_sphere;
    return my_sphereshape;

  }

  public void shape(final Shape the_shape) {
    my_sphereshape = the_shape;

  }
}
