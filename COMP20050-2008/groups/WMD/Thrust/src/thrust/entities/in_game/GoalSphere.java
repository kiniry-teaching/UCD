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
 * @author Siobhan Dunne (siobhan.dunne@ucdconnect.ie)
 * @version 1 May 2008
 */
public class GoalSphere extends DynamicEntity
  implements NeutralEntity, Tow {

  /**
   * The color of a goal sphere.
   */
  Color my_color;

  /**
   * The shape of a goal sphere.
   */
  Shape my_shape;

  /**
   * Make a goal sphere.
   */
  public GoalSphere(final double[] a_position,
                    final double an_orientation,
                    final double[] an_acceleration,
                    final double a_mass,
                    final double[] a_velocity,
                    //final String an_initial_shape_name,
                    //final Shape an_initial_shape,
                    final byte an_initial_state) {

    super();
    color(Color.GREEN);
    //my_shape = circle;
    super.set_Dynamic_State(a_position, an_orientation, an_acceleration,
                            a_mass, a_velocity, "Circle",
                            my_shape, an_initial_state);

  }

  public void tow() {
    // TODO Auto-generated method stub

  }

  public boolean towed() {
    // TODO Auto-generated method stub
    return false;
  }


  public double momentum() {
    // TODO Auto-generated method stub
    return 0;
  }

  public Color color() {
    return my_color;
  }

  public void color(final Color the_color) {
    my_color = the_color;
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
