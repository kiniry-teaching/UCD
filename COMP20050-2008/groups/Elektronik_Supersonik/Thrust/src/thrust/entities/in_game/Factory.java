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

import java.awt.Shape;

import thrust.animation.Animatable;
import thrust.animation.Animation;
import thrust.animation.EntityAnimation;
import thrust.entities.EnemyAI;
import thrust.entities.EnemyEntity;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;
import thrust.entities.behaviors.AI;

/**
 * An enemy factory.
 * @author Elektronik Supersonik (.@.)
 * @version 18 April 2008
 */
public class Factory extends StaticEntity
  implements EnemyEntity, Animatable {
  /**
  * An Integer storing our maximum velocity and acceleration.
  */
  public static final int HEALTH_LIMIT = 20;
  /**
   * Stores the health(hit-points) of the factory.
   */
  private transient byte my_health;
  /**
   * The factory's chimney.
   */
  private transient FactoryChimney my_chimney;
  /**
   * The factory's sphere.
   */
  private transient FactorySphere my_sphere;
  /**
   * The AI of the factory.
   */
  private final EnemyAI my_ai;
  /**
   * The animation of the factory.
   */
  private transient EntityAnimation my_animation;

  public Factory(final double[] the_position, final double the_orientation,
                 final double[] the_acceleration, final double the_mass,
                 final double[] the_velocity,
                 final String the_initial_shape_name,
                 final Shape the_initial_shape, final byte the_initial_state) {
    super();
    super.set_state(the_position, the_orientation, the_acceleration, the_mass,
                    the_velocity, the_initial_shape_name, the_initial_shape,
                    the_initial_state);
    my_chimney = new FactoryChimney();
    my_sphere = new FactorySphere();
    my_health = HEALTH_LIMIT;
    my_ai = new EnemyAI();
    my_animation = new EntityAnimation();
  }

  public AI attack() {
    return my_ai.attack();
  }

  public void attack(final AI the_behavior) {
    my_ai.attack(the_behavior);
  }

  public AI disturb() {
    return my_ai.disturb();
  }

  public void disturb(final AI the_behavior) {
    my_ai.disturb(the_behavior);
  }

  public void animate() {
    my_animation.animate();
  }

  public Animation animation() {
    return my_animation.animation();
  }

  public void animation(final Animation the_animation) {
    my_animation.animation(the_animation);
  }
  /**
   * @return How much damage have you sustained?
   */
  //@ ensures 0 <= \result & \result <= 20;
  public /*@ pure @*/ byte damage() {
    byte ret = (byte) (HEALTH_LIMIT - my_health);
    if (ret < 0) {
      ret = 0;
    }
    return ret;
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
    my_health = (byte) (my_health - the_damage);
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

  //@ public invariant (* See constraint on colour in FactoryChimney. *);
  //@ public invariant colour() == chimney().colour();

  /**
   * A chimney of a factory.
   * @author Joe Kiniry (kiniry@acm.org)
   * @version 18 April 2008
   */
  public class FactoryChimney extends StaticEntity
    implements EnemyEntity, Animatable {
    /**
     * Indicates whether the chimney is smoking.
     */
    private transient boolean my_smoking;
    /**
     * The AI of the chimney.
     */
    private transient EnemyAI my_ai;
    /**
     * The animation of the chimney.
     */
    private transient EntityAnimation my_animation;
    public FactoryChimney() {
      super();
      my_ai = new EnemyAI();
      my_animation = new EntityAnimation();
    }
    public AI attack() {
      return my_ai.attack();
    }

    public void attack(final AI the_behavior) {
      my_ai.attack(the_behavior);
    }

    public AI disturb() {
      return my_ai.disturb();
    }

    public void disturb(final AI the_behavior) {
      my_ai.disturb(the_behavior);
    }

    public void animate() {
      my_animation.animate();
    }

    public Animation animation() {
      return my_animation.animation();
    }

    public void animation(final Animation the_animation) {
      my_animation.animation(the_animation);
    }
    /**
     * @return Are you smoking?
     */
    public /*@ pure @*/ boolean smoking() {
      return my_smoking;
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

    /*@ public invariant (* A factories chimney is the same colour as
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
    /*@ public invariant (* A factory sphere's colour is always green. *);
      @ public invariant colour() == java.awt.Color.GREEN;
      @ public invariant (* The goal sphere is not destroyed by a
      @                     factory's sphere. *);
      @*/
    public FactorySphere() {
      super();
    }
  }
}
