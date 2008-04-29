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
import javax.swing.Timer;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import thrust.animation.Animatable;
import thrust.animation.Animation;
import thrust.entities.EnemyEntity;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;
import thrust.entities.behaviors.AI;

/**
 * An enemy factory.
 * @author David Maguire (David.Maguire.2@ucdconnect.ie)
 * @version 18 April 2008
 */
public class Factory extends StaticEntity
  implements EnemyEntity, Animatable {
  /**the amount of damage sustain by the factory.*/
  private byte my_damage;
  /**how often the timer will go off.*/
  private final int my_second = 1000;
  /**the chimney that the factory has.*/
  private FactoryChimney my_chimney;
  /**the sphere that the factory has.*/
  private FactorySphere my_sphere;
  /**the health of the factory.*/
  private double my_health;
  /**Color of the factory.*/
  private Color my_color;
  /**a static entity.*/
  private StaticEntity my_entity;
  /**the mass of the factory.*/
  private double my_mass;

  public Factory(final double[] the_position,
                 final double the_orientation,
                 final double[] the_acceleration,
                 final double the_mass,
                 final double[] the_velocity,
                 final String the_shapename,
                 final Shape the_shape,
                 final byte the_state) {

    super();
    super.set_Staticstate(the_position, the_orientation,
                          the_acceleration, the_mass,
                          the_velocity, the_shapename,
                          the_shape, the_state);
    my_mass = the_mass;
  }
  /**
   * @return How much damage have you sustained?
   */
  //@ ensures 0 <= \result & \result <= 20;
  public /*@ pure @*/ byte damage() {
    final int twenty = 20;

    if (my_damage < 0) {
      return 0;
    }
    if (my_damage > twenty) {
      return twenty;

    } else {
      return my_damage;
    }
  }

  public void health(final double the_health) {
    my_health = the_health;
  }

  public double health() {
    return my_health - my_damage;
  }
  /**listens out for the event.*/
  class Listener implements ActionListener {
    public void actionPerformed(final ActionEvent the_event) {
      my_health++;
      my_damage--;
    }
  }

  public void timer() {
    final Listener my_listener = new Listener();
    final Timer my_timer = new Timer(my_second, my_listener);
    my_timer.start();
  }
  /**
   * @return What is your chimney?
   */
  public /*@ pure @*/ FactoryChimney chimney() {
    return my_chimney;
  }

  /**
   * @return What is your sphere?
   */
  public /*@ pure @*/ FactorySphere sphere() {
    return my_sphere;
  }

  /**
   * @param the_damage You have sustained this many units of damage.
   */
  //@ requires 0 <= the_damage;
  //@ ensures damage() == \old(damage() - the_damage);
  public void damage(final byte the_damage) {
    my_damage = the_damage;
  }

  public Color color() {
    return my_color;
  }

  public void color(final Color the_color) {
    my_color = the_color;
  }

  /*@ public invariant (* All factories have exactly one sphere and
    @                     one chimney. *);
    @ public invariant (* A bullet causes 1 unit of damage. *);
    @ public invariant (* Each second 1 unit of damage is eliminated. *);
    @ public initially (* A factory initially has zero units of damage. *);
    @ public initially damage() == 0;
    @ public invariant (* A factory can sustain 20 units of damage before
    @                     it is destroyed. *);
    @ public invariant (* A factory with more than 10 units of damage
    @                     has a chimney that does not smoke. *);
    @ public invariant 10 < damage() ==> !chimney().smoking();
    @ public invariant (* A factory with at most 10 units of damage has
    @                     a smoking chimney. *);
    @ public invariant damage() <= 10 ==> chimney().smoking();
    @*/

  //@ public invariant (* See constraint on color in FactoryChimney. *);
  //@ public invariant color() == chimney().color();

  /**
   * A chimney of a factory.
   * @author Joe Kiniry (kiniry@acm.org)
   * @version 18 April 2008
   */
  public class FactoryChimney extends StaticEntity
    implements EnemyEntity, Animatable {
    /**holds whether or not the chimney is smoking.*/
    private boolean my_smoking;
    /**chimney's colour.*/
    private Color my_color;
    /**the factory the chimney is attached to.*/
    private Factory my_factory;
    /**a static entity.*/
    private StaticEntity my_entity;
    /**the mass of the chimney.*/
    private double my_mass;

    public FactoryChimney(final Factory the_factory, final double the_mass) {

      my_factory = the_factory;
      my_color = my_factory.color();
      my_mass = the_mass;
    }
    /**
     * @return Are you smoking?
     */
    public /*@ pure @*/ boolean smoking() {
      return (my_smoking);
    }

    /**
     * Your smoking state is dictated by this flag.
     * @param the_smoking_state A flag indicating whether the chimney
     * is smoking or not.
     */
    //@ ensures smoking() <==> the_smoking_state;
    public void smoking(final boolean the_smoking_state) {
      my_smoking = the_smoking_state;
    }

    public Color color() {
      return my_color;
    }
    public AI attack() {
      // TODO Auto-generated method stub
      return null;
    }
    public void attack(final AI the_behavior) {
      // TODO Auto-generated method stub

    }
    public AI disturb() {
      // TODO Auto-generated method stub
      return null;
    }
    public void disturb(final AI the_behavior) {
      // TODO Auto-generated method stub

    }
    public void animate() {
      // TODO Auto-generated method stub

    }
    public Animation animation() {
      // TODO Auto-generated method stub
      return null;
    }
    public void animation(final Animation the_animation) {
      // TODO Auto-generated method stub

    }
    public void acceleration(final double[] the_acceleration) {
      my_entity.acceleration(the_acceleration);
    }
    public double gravitational_constant() {
      return my_entity.gravitational_constant();
    }
    public void mass(final double the_mass) {
      my_mass = the_mass;

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
    public void color(final Color the_color) {
      my_entity.color(the_color);

    }

    /*@ public invariant (* A factories chimney is the same color as
      @                     its factory. *);
      @ public invariant (* The goal sphere is destroyed by a
      @                     factory's chimney. *);
      @ public invariant (* The spaceship is destroyed by a factory's
      @                     chimney. *);
      @*/
  }

  /**
   * A sphere of a factory.
   * @author Joe Kiniry (kiniry@acm.org)
   * @version 18 April 2008
   */
  public class FactorySphere extends StaticEntity
    implements NeutralEntity {
    /**the mass of the sphere.*/
    private double my_mass;
    /**the factory that the sphere is attached to.*/
    private Factory my_factory;
    /**the color of the sphere.*/
    private final Color my_color = java.awt.Color.GREEN;
    /**a static entity.*/
    private StaticEntity my_entity;

    public FactorySphere(final Factory the_factory, final double the_mass) {
      my_factory = the_factory;
      my_mass = the_mass;
    }

    public Color color() {
      return my_color;
    }

    public void acceleration(final double[] the_acceleration) {
      my_entity.acceleration(the_acceleration);

    }

    public double gravitational_constant() {
      return my_entity.gravitational_constant();
    }

    public void mass(final double the_mass) {
      my_mass = the_mass;

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

    public void color(final Color the_color) {


    }

    /*@ public invariant (* A factory sphere's color is always green. *);
      @ public invariant color() == java.awt.Color.GREEN;
      @ public invariant (* The goal sphere is not destroyed by a
      @                     factory's sphere. *);
      @*/
  }

  public AI attack() {
    // TODO Auto-generated method stub
    return null;
  }
  public void attack(final AI the_behavior) {
    // TODO Auto-generated method stub

  }
  public AI disturb() {
    // TODO Auto-generated method stub
    return null;
  }
  public void disturb(final AI the_behavior) {
    // TODO Auto-generated method stub

  }
  public void animate() {
    // TODO Auto-generated method stub

  }
  public Animation animation() {
    // TODO Auto-generated method stub
    return null;
  }
  public void animation(final Animation the_animation) {
    // TODO Auto-generated method stub

  }
  public void acceleration(final double[] the_acceleration) {
    my_entity.acceleration(the_acceleration);

  }
  public double gravitational_constant() {
    return my_entity.gravitational_constant();
  }
  public void mass(final double the_mass) {
    my_mass = the_mass;

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
}
