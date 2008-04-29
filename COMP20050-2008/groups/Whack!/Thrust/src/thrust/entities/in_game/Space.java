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

import thrust.animation.AnimatableWhack;
import thrust.animation.Animatable;
import thrust.animation.Animation;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;

/**
 * The vacuum in which entities exist.
 * @author David Magurie (David.Maguire.2@ucdconnect.ie)
 * @version 18 April 2008
 */
public class Space extends StaticEntity
  implements NeutralEntity, Animatable {
  /**the stars in space.*/
  private Star[] my_stars;
  /**a static entity.*/
  private StaticEntity my_entity;
  /**an animatable thing.*/
  private AnimatableWhack my_whack;

  public Space(final Star[] the_stars) {
    my_stars = the_stars;
  }
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
  public void add_star(final Star the_star) {
    final int length = my_stars.length;
    my_stars[length - 1] = the_star;
  }

  public double[] acceleration() {
    return my_entity.acceleration();
  }

  public double mass() {
    // TODO Auto-generated method stub
    return 0;
  }

  public double momentum() {
    return my_entity.momentum();
  }

  public double[] velocity() {
    return my_entity.velocity();
  }

  public void render() {
    // TODO Auto-generated method stub

  }

  public Shape shape() {
    return my_entity.shape();
  }

  public void shape(final Shape the_shape) {
    my_entity.shape(the_shape);
  }

  public String shape_name() {
    return my_entity.shape_name();
  }

  public byte state() {
    return my_entity.state();
  }

  public void state(final byte the_state) {
    my_entity.state(the_state);

  }

  public void animate() {
    my_whack.animate();

  }

  public Animation animation() {
    return my_whack.animation();
  }

  public void animation(final Animation the_animation) {
    my_whack.animation(the_animation);

  }

  public Color color() {
    return my_entity.color();
  }

  public void color(final Color the_color) {
    my_entity.color(the_color);
  }
  public void acceleration(final double[] the_acceleration) {
    my_entity.acceleration(the_acceleration);

  }
  public double gravitational_constant() {
    return 0;
  }
  public void mass(final double the_mass) {
    my_entity.mass(the_mass);

  }
  public void orientation(final double the_orientation) {
    my_entity.orientation(the_orientation);

  }
  public void position(final double[] the_position) {
    my_entity.position(the_position);

  }
  public void simulate(final double some_seconds) {
    my_entity.simulate(some_seconds);

  }
  public void velocity(final double[] the_velocity) {
    my_entity.velocity(the_velocity);

  }

  //@ public invariant (* Terrain and space are disjoint. *);
}
