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
  implements EnemyEntity, Animatable {
  /** How much damage can this factory take before exploding? */
  private static final byte MAXIMUM_DAMAGE = 20;

  /** The number of frames to render before fixing one unit of damage. */
  private static final int FRAMES_PER_UNIT_OF_DAMAGE_REPAIR = 5;

  /** The amount of damage necessary to make a factory stop smoking. */
  private static final int BROKEN_FACTORY_DAMAGE_LEVEL = 10;

  /** The amount of damage this factory has sustained. */
  private transient byte my_damage;

  /** This factory's chimney. */
  private final transient /*@ non_null @*/ FactoryChimney my_chimney;

  /** This factory's sphere. */
  private final transient /*@ non_null @*/ FactorySphere my_sphere;

  /** A counter used to decrease damage over time. */
  private transient int my_counter;

  /** Create a new factory, complete with smoking chimney and sphere. */
  public Factory() {
    super();
    my_chimney = new FactoryChimney(this);
    my_sphere = new FactorySphere(this);
  }

  /** @return How much damage have you sustained? */
  //@ ensures 0 <= \result & \result <= MAXIMUM_DAMAGE;
  public /*@ pure @*/ byte damage() {
    return my_damage;
  }

  /** @return What is your chimney? */
  public /*@ pure @*/ FactoryChimney chimney() {
    return my_chimney;
  }

  /** @return What is your sphere? */
  public /*@ pure @*/ FactorySphere sphere() {
    return my_sphere;
  }

  /** @param the_damage You have sustained this many units of damage. */
  //@ requires 0 <= the_damage;
  //@ ensures damage() == \old(damage() + the_damage);
  public void damage(final byte the_damage) {
    my_damage += the_damage;
    if (BROKEN_FACTORY_DAMAGE_LEVEL <= my_damage) {
      my_chimney.smoking(false);
    }
  }

  public AI attack() {
    // skip
    return null;
  }

  public void attack(final AI the_behavior) {
    // ignore formal parameter and skip
  }

  public AI disturb() {
    // skip
    return null;
  }

  public void disturb(final AI the_behavior) {
    // ignore formal parameter and skip
  }

  public void animate() {
    chimney().animate();
    // every FRAMES_PER_UNIT_OF_DAMAGE_REPAIR frames one unit of
    // damage is erased
    my_counter++;
    if ((my_counter % FRAMES_PER_UNIT_OF_DAMAGE_REPAIR == 0) &
        (0 < my_damage)) {
      my_damage--;
      if (my_damage == (BROKEN_FACTORY_DAMAGE_LEVEL - 1)) {
        my_chimney.smoking(true);
      }
    }
  }

  public Animation animation() {
    // skip
    return null;
  }

  public void animation(final Animation the_animation) {
    // ignore formal parameter and skip
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
    /** The factory associated with this chimney. */
    private final transient /*@ non_null @*/ Factory my_factory;

    /** Am I smoking? */
    private transient boolean my_smoking_state = true;

    /**
     * Create a new chimney for the given factory.
     * @param the_factory this chimney's factory.
     */
    public FactoryChimney(final /*@ non_null @*/ Factory the_factory) {
      super();
      my_factory = the_factory;
    }

    /** @return Are you smoking? */
    public /*@ pure @*/ boolean smoking() {
      return my_smoking_state;
    }

    /**
     * Your smoking state is dictated by this flag.
     * @param the_smoking_state A flag indicating whether the chimney
     * is smoking or not.
     */
    //@ ensures smoking() <==> the_smoking_state;
    public void smoking(final boolean the_smoking_state) {
      my_smoking_state = the_smoking_state;
    }

    public AI attack() {
      // skip
      return null;
    }

    public void attack(final AI the_behavior) {
      // ignore formal parameter and skip
    }

    public AI disturb() {
      // skip
      return null;
    }

    public void disturb(final AI the_behavior) {
      // ignore formal parameter and skip
    }

    public void animate() {
      my_chimney.animate();
    }

    public Animation animation() {
      // skip
      return null;
    }

    public void animation(final Animation the_animation) {
      // ignore formal parameter value and skip
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
    /** The factory associated with this sphere. */
    private final transient /*@ non_null @*/ Factory my_factory;

    /*@ public invariant (* A factory sphere's color is always green. *);
      @ public invariant color() == java.awt.Color.GREEN;
      @ public invariant (* The goal sphere is not destroyed by a
      @                     factory's sphere. *);
      @*/

    /** Create a new sphere. */
    public FactorySphere(final /*@ non_null @*/ Factory the_factory) {
      super();
      my_factory = the_factory;
    }
  }
}
