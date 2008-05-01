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
import thrust.entities.FriendEntity;
import thrust.entities.about.Fuelable;
import thrust.entities.behaviors.Tow;

/**
 * The player's main vehicle.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Spaceship extends DynamicEntity
  implements FriendEntity, Fuelable, Tow {
  /*@ public invariant (* A spaceship's mass when empty of all fuel is
    @                     10000kg. *);
    @ public invariant EMPTY_MASS <= mass();
    @*/
  /** A spaceship's mass when empty of all fuel is 10000kg. */
  public static final int EMPTY_MASS = 10000;

  /*@ public initially (* The spaceship's initial fuel is 1000 units. *);
    @ public initially fuel() == INITIAL_FUEL;
    @*/
  /** The spaceship's initial fuel is 1000 units. */
  public static final int INITIAL_FUEL = 1000;
  private int my_fuel;

  /* (non-Javadoc)
   * @see thrust.entities.about.Fuelable#change_fuel_content(int)
   */
  public void change_fuel_content(final int the_fuel_change) {
    if (my_fuel + the_fuel_change < 0)
    {
      my_fuel = 0;
    }

    if (my_fuel + the_fuel_change > maximum_fuel())
    {
      my_fuel = (int) maximum_fuel();
    }
    my_fuel = my_fuel + the_fuel_change;

  }

  /* (non-Javadoc)
   * @see thrust.entities.about.Fuelable#fuel_mass()
   */
  public int fuel_mass() {
    // TODO Auto-generated method stub
    return 0;
  }

  /* (non-Javadoc)
   * @see thrust.entities.about.Fuelable#fuel()
   */
  public float fuel() {
    my_fuel = (int) maximum_fuel();
    return my_fuel;
  }

  /* (non-Javadoc)
   * @see thrust.entities.about.Fuelable#maximum_fuel()
   */
  public float maximum_fuel() {
    final float maximum_fuel = Float.POSITIVE_INFINITY;
    return maximum_fuel;
  }

  /* (non-Javadoc)
   * @see thrust.entities.about.Fuelable#set_fuel_content(int)
   */
  public void set_fuel_content(int the_fuel_content) {
    if (the_fuel_content >= 0 && the_fuel_content <= maximum_fuel())
    {
      my_fuel = the_fuel_content;
    }
  }

  /* (non-Javadoc)
   * @see thrust.entities.behaviors.Tow#tow()
   */
  public void tow() {
    // TODO Auto-generated method stub
    
  }

  /* (non-Javadoc)
   * @see thrust.entities.behaviors.Tow#towed()
   */
  public boolean towed() {
    // TODO Auto-generated method stub
    return false;
  }

  /* (non-Javadoc)
   * @see thrust.entities.properties.GameColor#color()
   */
  public Color color() {
    // TODO Auto-generated method stub
    return null;
  }

  /* (non-Javadoc)
   * @see thrust.entities.properties.GameColor#color(java.awt.Color)
   */
  public void color(Color the_color) {
    // TODO Auto-generated method stub
    
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#acceleration()
   */
  public double[] acceleration() {
    // TODO Auto-generated method stub
    return null;
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#acceleration(double[])
   */
  public void acceleration(double[] the_acceleration) {
    // TODO Auto-generated method stub
    
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#gravitational_constant()
   */
  public double gravitational_constant() {
    // TODO Auto-generated method stub
    return 0;
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#mass()
   */
  public double mass() {
    // TODO Auto-generated method stub
    return 0;
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#mass(double)
   */
  public void mass(double the_mass) {
    // TODO Auto-generated method stub
    
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#momentum()
   */
  public double momentum() {
    // TODO Auto-generated method stub
    return 0;
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#orientation()
   */
  public double orientation() {
    // TODO Auto-generated method stub
    return 0;
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#orientation(double)
   */
  public void orientation(double the_orientation) {
    // TODO Auto-generated method stub
    
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#position()
   */
  public double[] position() {
    // TODO Auto-generated method stub
    return null;
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#position(double[])
   */
  public void position(double[] the_position) {
    // TODO Auto-generated method stub
    
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#simulate(double)
   */
  public void simulate(double some_seconds) {
    // TODO Auto-generated method stub
    
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#velocity()
   */
  public double[] velocity() {
    // TODO Auto-generated method stub
    return null;
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#velocity(double[])
   */
  public void velocity(double[] the_velocity) {
    // TODO Auto-generated method stub
    
  }

  public void change_fuel_content(float the_fuel_change) {
    // TODO Auto-generated method stub
    
  }

  public void set_fuel_content(float the_fuel_content) {
    // TODO Auto-generated method stub
    
  }

  /*@ public invariant (* The spaceship is destroyed by the barrier. *);
    @ public invariant (* The spaceship is destroyed by a bullet. *);
    @ public invariant (* The spaceship is destroyed by the factory. *);
    @ public invariant (* The spaceship is destroyed by the fuel pod. *);
    @ public invariant (* If the spaceship is towing the goal sphere,
    @                     and the spaceship is destroyed, the goal
    @                     sphere is also destroyed. *);
    @ public invariant (* The spaceship is destroyed by the gun turret. *);
    @ public invariant (* The spaceship is not affected by space. *);
    @ public invariant (* The spaceship is not affected by a star. *);
    @ public invariant (* The spaceship is destroyed by the terrain. *);
    @ public invariant (* A spaceship's mass is the sum of its empty mass,
    @                     plus the mass of its fuel, plus the mass of
    @                     the goal sphere, if it is being towed. *);
    @ public invariant mass() == EMPTY_MASS + fuel_mass() +
    @                  (towed() ? GoalSphere.MASS : 0);
    @ public invariant (* The spaceship's shape is always that of a ship. *);
    @ public invariant (* The spaceship's color is always white. *);
    @ public invariant color() == java.awt.Color.WHITE;
    @*/
}
