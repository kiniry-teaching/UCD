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

import thrust.animation.Animatable;
import thrust.animation.Animation;
import thrust.entities.EnemyEntity;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;
import thrust.entities.behaviors.AI;

/**
 * An enemy factory.
 * @author Joe Kiniry (kiniry@acm.org)
 * Edited by Roger Thomas.
 * @version 28 April 2008
 */

public class Factory extends StaticEntity
  implements EnemyEntity, Animatable {
  /**
   * @return How much damage have you sustained?
   */
  //@ ensures 0 <= \result & \result <= 20;
  private byte my_damage;
  /**
   * The frames in the explosion animation.
   */
  private Animation my_animation;
  /**
   * The color of the Factory.
   */
  private Color my_color;
  /**
   * The AI of an attacking factory.
   */
  private AI my_attackAI;
  /**
   * The ai of a disturbing factory.
   */
  private AI my_disturbAI;
  public /*@ pure @*/ byte damage() {
    return my_damage;
  }
  /**
   * @return What is your chimney?
   */
  public /*@ pure @*/ FactoryChimney chimney() {
    return null;
  }

  /**
   * @return What is your sphere?
   */
  public /*@ pure @*/ FactorySphere sphere() {
    return null;
  }
  /**
   * @return null
   * Factory has no AI
   */
  public void attack(final AI the_behaviour) {
    my_attackAI = the_behaviour;
  }
 /**
  * @return null
  * Factory has no AI
  */
  public void disturb(final AI the_behaviour) {
    my_disturbAI = the_behaviour;
  }
  public AI attack() {
    return my_attackAI;
  }
  public AI disturb() {
    return my_disturbAI;
  }
  public double gravitational_constant() {
    final double d = 9.81;
    return d;
  }
  public void animation(final Animation the_animation)
  {
    my_animation = the_animation;
  }
  public Animation animation()
  {
    return my_animation;
  }
  public void animate() {
  }

  /**
   * @param the_damage You have sustained this many units of damage.
   */
  //@ requires 0 <= the_damage;
  //@ ensures damage() == \old(damage() - the_damage);
  public void damage(final byte the_damage) {
    my_damage = the_damage;
  }
  public void color(final Color the_color) {
  }
  public Color color() {
    return my_color;
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

  public void simulate(final double the_amount) {
  }
  /**
   * A chimney of a factory.
   * @author Joe Kiniry (kiniry@acm.org)
   * @version 18 April 2008
   */
  public class FactoryChimney extends StaticEntity
    implements EnemyEntity, Animatable {
    /**
     * The frames in the explosion animation.
     */
    private Animation my_animation;
    /**
     * The smoking animation.
     */
    private Animation my_smoking_animation;
    /**
     * The color of the Factory Chimney.
     */
    private Color my_color;
    /**
     * Boolean defines whether the factory should be smoking or not.
     */
    private boolean my_isSmoking;
    /**
     * @return Are you smoking?
     */
    public /*@ pure @*/ boolean smoking() {
      return my_isSmoking;
    }
    /**
     * Start the smoking animation.
     */
    public void start_smoking() {
      if (my_isSmoking) {
        my_smoking_animation.start();
      }
    }
    public void stop() {
      if (!my_isSmoking) {
        my_smoking_animation.stop();
      }
    }
    /**
     * @return null
     * Factory has no AI
     */
    public void attack(final AI the_behaviour) {
      my_attackAI = the_behaviour;
    }
   /**
    * @return null
    * Factory has no AI
    */
    public void disturb(final AI the_behaviour) {
      my_disturbAI = the_behaviour;
    }
    public AI attack() {
      return my_attackAI;
    }
    public AI disturb() {
      return my_disturbAI;
    }
    public void animation(final Animation the_animation)
    {
      my_animation = the_animation;
    }
    public Animation animation()
    {
      return my_animation;
    }
    public void animate() {
    }
    public void simulate(final double the_amount) {
    }
    public double gravitational_constant() {
      final double d = 9.81;
      return d;
    }
    public void color(final Color the_color) {
    }
    public Color color() {
      return my_color;
    }
    /**
     * Your smoking state is dictated by this flag.
     * @param the_smoking_state A flag indicating whether the chimney
     * is smoking or not.
     */
    //@ ensures smoking() <==> the_smoking_state;
    public void smoking(final boolean the_smoking_state) {
      my_isSmoking = the_smoking_state;
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
    /**
     * The color of the Factory Chimney.
     */
    private Color my_color;
    public void color(final Color the_color) {
    }
    public Color color() {
      return my_color;
    }
    public void simulate(final double the_amount) {
    }
    public double gravitational_constant() {
      final double d = 9.81;
      return d;
    }
    /*@ public invariant (* A factory sphere's color is always green. *);
      @ public invariant color() == java.awt.Color.GREEN;
      @ public invariant (* The goal sphere is not destroyed by a
      @                     factory's sphere. *);
      @*/
  }
}
