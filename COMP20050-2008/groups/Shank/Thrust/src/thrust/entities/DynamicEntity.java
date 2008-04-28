/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 * Edit Ben Fitzgerald on 24/04/2008
 */

package thrust.entities;
import java.awt.Color;
import java.awt.Shape;

import thrust.physics.PhysicsInterface;

/**
 * Entities whose position or orientation change.
 * @author Ben Fitzgerald  (ben.fitz@hotmail.com)
 * @version 24 April 2008
 *  Edited by Ben Fitzgerald 28/04/2008
 */
public abstract class DynamicEntity extends Entity
  implements PhysicsInterface {
/**The entities x and y position.*/
  private double[] my_position;
/**The entities orientation in radians.*/
  private double my_orientation;
/**The entities colour.*/
  private Color my_colour;
/**The entities shape name.*/
  private String my_initial_shape_name;
/**The entities shape.*/
  private Shape my_initial_shape;
/**The entities initial state.*/
  private byte my_initial_state;
/**The entities acceleration.*/
  private double[] my_acceleration;
/**The entities velocity.*/
  private double[] my_velocity;
/**The entities mass.*/
  private double my_mass;
/**The entities momentum.*/
  private double my_momentum;

/**Set the initial.*/
  public void set_State(final double[] the_position,
                                        final double the_orientation,
                                        final Color the_colour,
                                        final String the_initial_shape_name,
                                        final Shape the_initial_shape,
                                        final byte the_initial_state
  )
  {
    super.set_state(the_initial_shape_name, the_initial_shape,
                    the_initial_state);
    my_position = the_position;
    my_orientation = the_orientation;
    my_colour = the_colour;
  }

  /**
   * @param This is your position.
   * */
  public void position(final double[] the_position)
  {
    my_position = the_position;
  }
  /**
   * @return What position do you have?
   * */
  public double[] position()
  {
    return my_position;
  }

  /**
   * @param his is your orientation.
   * */
  public void orientation(final double the_orientation)
  {
    my_orientation = the_orientation;
  }
  /**
   * @return What orientation do you have?
   * */
  public double orientation()
  {
    return my_orientation;
  }

  /**
   * @return Set entity colour.
   * */
  public void colour(final Color the_colour)
  {
    my_colour = the_colour;
  }
  /**
   * @return What colour do you have?
   * */
  public Color colour()
  {
    return my_colour;
  }

  /**
   * @return What initial_shape_name do you have?
   * */
  public String initial_shape_name()
  {
    return my_initial_shape_name;
  }
  /**
   * @return What initial_shape do you have?
   * */
  public Shape initial_shape()
  {
    return my_initial_shape;
  }
  /**
   * @return What initial_state do you have?
   * */
  public byte initial_state()
  {
    return my_initial_state;
  }

  /**
   * @param This is your acceleration.
   * */
  public void acceleration(final double[] the_acceleration)
  {
    my_acceleration = the_acceleration;
  }
  /**
   * @return What acceleration do you have?
   * */
  public double[] acceleration()
  {
    return my_acceleration;
  }

  /**
   * @param  This is your velocity.
   * */
  public void velocity(final double[] the_velocity)
  {
    my_velocity = the_velocity;
  }
  /**
   * @return What velocity do you have?
   * */
  public double[] velocity()
  {
    return my_velocity;
  }

  /**
   * @param This is your mass.
   * */
  public void mass(final double the_mass)
  {
    my_mass =  the_mass;
  }
  /**
   * @return What mass do you have?
   * */
  public double mass()
  {
    return my_mass;
  }

  /**
   * @return What momentum do you have?
   * */
  public double momentum()
  {
    return my_momentum;
  }

  /**
   * Simulate yourself for this many seconds.
   * @param Simulate yourself for this many seconds.
   * */
  public void simulate(final int the_run_time)
  {
    //TODO simulation method.
  }
}
