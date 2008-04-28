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

import thrust.animation.Animatable;
import thrust.animation.Animation;
import thrust.entities.EnemyEntity;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;
import thrust.entities.behaviors.AI;

/**
 * An enemy factory.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Factory extends StaticEntity
  implements EnemyEntity { // Removed implements Animatable => FactorySmoke

  /** Byte holding current hit points of Factory. */
  private static byte my_hp;
  /** Byte holding starting hit points of Factory. */
  private static byte my_starting_hp;
  /** Instance of FactoryChimney class associated with this Factory. */
  private FactoryChimney my_factorychimney;
  /** Instance of FactorySphere class associated with this Factory. */
  private FactorySphere my_factorysphere;
  /** Instance of AI class implemented in EnemyEntity. */
  private AI my_ai;

  /**
   * @return How much damage have you sustained?
   */
  //@ ensures 0 <= \result & \result <= 20;
  public /*@ pure @*/ byte damage() {
    return (byte) (my_starting_hp - my_hp);
  }

  /**
   * @return What is your chimney?
   */
  public /*@ pure @*/ FactoryChimney chimney() {
    return my_factorychimney;
  }

  /**
   * @return What is your sphere?
   */
  public /*@ pure @*/ FactorySphere sphere() {
    return my_factorysphere;
  }

  /**
   * @param the_damage You have sustained this many units of damage.
   */
  //@ requires 0 <= the_damage;
  //@ ensures damage() == \old(damage() - the_damage);
  public void damage(final byte the_damage) {
    my_hp -= the_damage; // my_hp = my_hp - the_damage
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
    @ public invariant 10 < damage() ==> !chimney.smoking();
    @ public invariant (* A factory with at most 10 units of damage has
    @                     a smoking chimney. *);
    @ public invariant damage() <= 10 ==> chimney.smoking();
    @*/

  //@ public invariant (* See constraint on color in FactoryChimney. *);
  //@ public invariant color() == chimney().color();
  /**
   * @return What is your attack behavior AI?
   */
  public /*@ pure @*/ AI attack() {
    return my_ai.attack();
  }

  /**
   * @return What is your disturb behavior AI?
   */
  public /*@ pure @*/ AI disturb() {
    return my_ai.disturb();
  }

  /**
   * @param the_behavior This is your attack behavior.
   */
  //@ ensures attack() == the_behavior;
  public void attack(final AI the_behavior) {
    my_ai.attack(the_behaviour);
  }

  /**
   * @param the_behavior This is your disturb behavior.
   */
  //@ ensures disturb() == the_behavior;
  public void disturb(final AI the_behavior) {
    my_ai.disturb(the_behaviour)
  }

  /**
   * A chimney of a factory.
   * @author Joe Kiniry (kiniry@acm.org)
   * @version 18 April 2008
   */
  public class FactoryChimney extends StaticEntity
    implements EnemyEntity, Animatable {

    /** Boolean holding whether Chimney is smoking. */
    private boolean my_smoking_state;
    /** Animation holding animations for FactoryChimney class. */
    private Animation my_animation;
    /** AI holding behaviour for FactoryChimney class. */
    private AI my_ai;

    /**
     * @return Are you smoking?
     */
    public /*@ pure @*/ boolean smoking() {
      return my_smoking_state;
    }

    /** The animation methods. */
    
    public /*@ pure @*/ Animation animation() {
      return my_animation;
    }

    public void smoking(final boolean the_smoking_state) {
      my_smoking_state = the_smoking_state;
    }

    public void animation(final Animation the_animation) {
      my_animation = the_animation;
    }

    public void animate() {
      my_animation.animate(); // AnyAnimation.animate() UNFINISHED
    }

    /*@ public invariant (* A factories chimney is the same color as
      @                     its factory. *);
      @ public invariant (* The goal sphere is destroyed by a
      @                     factory's chimney. *);
      @ public invariant (* The spaceship is destroyed by a factory's
      @                     chimney. *);
      @*/

    /** The AI methods. */

    public /*@ pure @*/ AI attack() {
      return my_ai.attack();
    }

    public /*@ pure @*/ AI disturb() {
      return my_ai.disturb();
    }

    //@ ensures attack() == the_behavior;
    public void attack(final AI the_behavior) {
      my_ai.attack(the_behaviour);
    }

    //@ ensures disturb() == the_behavior;
    public void disturb(final AI the_behavior) {
      my_ai.disturb(the_behaviour);
    }
  }

  /**
   * A sphere of a factory.
   * @author Joe Kiniry (kiniry@acm.org)
   * @version 18 April 2008
   */
  public class FactorySphere extends StaticEntity
    implements NeutralEntity {
    /*@ public invariant (* A factory sphere's color is always green. *);
      @ public invariant color() == thrust.entities.properties.GameColor.GREEN;
      @ public invariant (* The goal sphere is not destroyed by a
      @                     factory's sphere. *);
      @*/
  }
}
