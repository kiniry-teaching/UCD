/*
 * A re-implementation of the classic C=64 game 'Thrust'. @author "Joe Kiniry
 * (kiniry@acm.org)" @module "COMP 20050, COMP 30050" @creation_date "March
 * 2007" @last_updated_date "April 2008" @keywords "C=64", "Thrust", "game"
 */
package thrust.entities.in_game;

import java.awt.Color;
import java.awt.Shape;

// import thrust.animation.Animation;
import thrust.entities.DynamicEntity;
import thrust.entities.EnemyEntity;
import thrust.entities.StaticEntity;
import thrust.entities.behaviors.AI;

/**
 * A bullet shot from the spaceship or a gun turret.
 *
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Bullet extends DynamicEntity implements EnemyEntity {
  /*
   * (non-Javadoc)
   *
   * @see thrust.physics.PhysicsInterface#mass()
   */
  /** holds the position. */
  private transient double[] my_position;
  /** holds the orientation. */
  private transient double my_orientation;
  /** holds the acceleration. */
  private transient double[] my_acceleration;
  /** holds the mass. */
  private transient double my_mass;
  /** holds the time. */
  private transient double my_time;
  /** holds the velocity. */
  private transient double[] my_velocity;
  /** the name of the shape. */
  private transient String my_shapename;
  /** the shape of the bullet. */
  private transient Shape my_shape;
  /** the state of the bullet. */
  private transient byte my_state;
  /** the colour of the bullet. */
  private transient Color my_color;
  /** the entity. */
  private transient StaticEntity my_entity;
  /** the time. */
  //private double my_time;
  /** the behaviour of the bullet. */
  private transient AI my_behavior;

  public Bullet(final double[] the_position, final double the_orientation,
      final double[] the_acceleration, final double the_mass,
      final double[] the_velocity, final String the_shapename,
      final Shape the_shape, final byte the_state) {
    super();
    super.Dynamic_State(the_position, the_orientation, the_acceleration,
                        the_mass, the_velocity, the_shapename, the_shape,
                        the_state);

  }

  // @ also ensures \result == 1;
  public double mass() {
    my_mass = 1;
    return my_mass;
  }

  public void mass(final double the_mass) {
    my_entity.mass(the_mass);
  }

  public void render() {
    // TODO Auto-generated method stub

  }

  public String shapename() {

    return my_shapename;
  }

  public Shape shape() {

    return my_shape;
  }

  public void shape(final Shape the_shape) {
    my_shape = the_shape;
  }

  public String shape_name() {
    return "square";
  }

  public byte state() {
    return my_state;
  }

  public void state(final byte the_state) {
    my_state = the_state;

  }

  public AI attack() {
    return my_behavior;
  }

  public void attack(final AI the_behavior) {
    my_behavior = the_behavior;

  }

  public AI disturb() {
    // TODO Auto-generated method stub
    return null;
  }

  public void disturb(final AI the_behavior) {
    // TODO Auto-generated method stub

  }

  public double[] acceleration() {
    return new double[] {my_acceleration[0], my_acceleration[1] };
  }

  public void acceleration(final double[] the_acceleration) {
    my_entity.acceleration();
  }

  public double gravitational_constant() {
    return my_entity.gravitational_constant();
  }

  public double momentum() {
    return my_entity.momentum();
  }

  public double orientation() {
    return my_orientation;
  }

  public void orientation(final double the_orientation) {
    my_entity.orientation(the_orientation);
  }

  public double[] position() {
    return new double[] {my_position[0], my_position[1] };
  }

  public void position(final double[] the_position) {
    my_entity.position(the_position);
  }

  public void simulate(final double a_time_interval) {
    my_time = a_time_interval;

  }

  public double[] velocity() {
    return new double[] {my_velocity[0], my_velocity[1] };
  }

  public void velocity(final double[] the_velocity) {
    my_entity.velocity(the_velocity);
  }

  public Color color() {
    return my_color;
  }

  public void color(final Color the_color) {
    my_color = the_color;

  }

  /**
   * The Point class.
   * @author ursula
   *
   */
  public class Point {
    /**
     *
     */
    private final transient int my_x = (int) Math.random();
    /**
     *
     */
    private final transient int my_y = (int) Math.random();

    public Point(final int the_x, final int the_y) {

      my_x = the_x;
      my_y = the_y;

    }

    public boolean shot() {
      final int number = 2;
      boolean answer;
      if (my_x == number && my_y == number) {
        answer = true;
      } else {
        answer = false;
      }
      return answer;
    }
  }

  /*
   * @ public invariant (* Bullets are destroyed on contact with a @ barrier, a
   * factory, a fuel pod, the goal @ sphere, a gun turret, the spaceship, 
   * or the @
   * terrain. *); @
   */
  // @ public invariant (* Bullets have a mass of 1 kg. *);
}