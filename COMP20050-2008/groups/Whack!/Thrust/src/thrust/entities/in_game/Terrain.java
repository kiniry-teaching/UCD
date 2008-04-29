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

import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;

/**
 * The planet on which some entities rest.
 * @author Tara Flood (Tara.Flood@ucdconnect.ie)
 * @version 18 April 2008
 */
public class Terrain extends StaticEntity implements NeutralEntity {
  /**
   * implements as a static Entity.
   */
  StaticEntity my_staticent;
  /**
   * implementing mass.
   */
  double my_mass;
  /**
   * implementing orientation.
   */
  double my_orientation;
  /**
   * implementing position.
   */
  double[] my_position;
 /**
  * implementing color.
  */
  Color my_terraincolor;
  /**
   * time.
   */
  double my_time;
  public void acceleration(final double[] the_acceleration) {
    my_staticent.acceleration(the_acceleration);
  }

  public double gravitational_constant() {
    return my_staticent.gravitational_constant();
  }

  public double mass() {
    return my_mass;
  }

  public void mass(final double the_mass) {
    my_staticent.mass(the_mass);
  }
  public double orientation() {
    return my_orientation;
  }

  public void orientation(final double the_orientation) {
    my_staticent.orientation(the_orientation);

  }
  public double[] position() {
    return  my_position;
  }

  public void position(final double[] the_position) {
    my_staticent.position(the_position);
  }

  public void simulate(final double some_seconds) {
    my_time = some_seconds;
  }

  public void velocity(final double[] the_velocity) {
    my_staticent.velocity(the_velocity);
  }

  public Color color() {
    my_terraincolor.equals(Color.RED);
    return my_terraincolor;
  }

  public void color(final Color the_color) {
    my_terraincolor = the_color;
  }
  /*@ public invariant (* Terrain and space are disjoint. *);
    @ public invariant (* The shape of the terrain is rendered as a
    @                     sequence of horizontal lines. *);
    @*/


}
