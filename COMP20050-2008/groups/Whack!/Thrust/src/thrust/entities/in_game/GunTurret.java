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

import thrust.entities.EnemyEntity;
import thrust.entities.StaticEntity;
import thrust.entities.behaviors.AI;

/**
 * An enemy gun turret that shoots bullets at the spaceship.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class GunTurret extends StaticEntity
  implements EnemyEntity {
  /**
   * @author allison fallon(allison.fallon@ucdconnect.ie)
   */
  /**
   * Colour of GunTurret.
   */
  Color my_colour;

  public double[] acceleration() {
    // TODO Auto-generated method stub
    return null;
  }
  public void acceleration(final double[] the_acceleration) {

  }
  public void simulate(final double a_time_interval) {
    // TODO Auto-generated method stub

  }

  public double mass() {
    // TODO Auto-generated method stub
    return 0;
  }
  public void mass(final double the_mass) {

  }

  public double momentum() {
    // TODO Auto-generated method stub
    return 0;
  }

  public double[] velocity() {
    // TODO Auto-generated method stub
    return null;
  }
  public void velocity(final double[] the_velocity) {

  }
  public double gravitational_constant() {
    return 0;
  }
  public double[] position() {
    return null;
  }

  public void position(final double[] the_position) {

  }
  public void orientation(final double the_orientation) {



  }
  public double orientation() {

    return 0;

  }


  public void render() {
    // TODO Auto-generated method stub

  }

  public Shape shape() {
    // TODO Auto-generated method stub
    return null;
  }

  public void shape(final Shape the_shape) {
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

  public void state(final byte the_state) {
    // TODO Auto-generated method stub

  }

  public AI attack() {
    // TODO Auto-generated method stub
    return null;
  }

  public void attack(final AI the_behavior) {
    // TODO Auto-generated method stub

  }


  public Color color() {
    my_colour.equals(Color.GREEN);
    return my_colour;
  }

  public void color(final Color the_color) {
    my_colour = the_color;

  }

  /**
   * @return The turret's attack AI must shoot a bullet toward the spaceship.
   */


  /**
   * @return The turret's disturb AI must shoot a bullet in a random direction
   * away from the terrain.
   */
  public AI disturb() {
    assert false; //@ assert false;
    return null;
  }

  /**
   * @param the_behavior The turret's disturb AI must shoot a bullet
   * in a random direction away from the terrain.
   */
  public void disturb(final AI the_behavior) {
    assert false; //@ assert false;
  }

  /*@ public invariant (* A gun turret always resides on/adjacent to
    @                     the terrain. *);
    @ public invariant (* A gun turret's color is always green. *);
    @ public invariant color() == java.awt.Color.GREEN;
    @*/
}
