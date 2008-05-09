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
import thrust.physics.PhysicsClass;

/**
 * An enemy factory.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Factory extends StaticEntity
  implements EnemyEntity, Animatable {
  
  private PhysicsClass my_physics; 
  private AI my_attack;
  private AI my_disturb;
  private FactoryChimney my_chimney;
  private FactorySphere my_sphere;
  private Animation my_animation;
  private final static double FACTORY_MASS = 45000;
  private final static double FACTORY_POS_X = 400;
  private final static double FACTORY_POS_Y = 200;
  /**
   * Factory constructor.
   */
  public Factory(){
    my_physics = new PhysicsClass(FACTORY_POS_X, FACTORY_POS_Y, FACTORY_MASS);
    //my_animation = new Animation();
    my_attack = new AI();
    my_disturb = new AI();
    my_chimney = new FactoryChimney();
    my_sphere = new FactorySphere();
  }
  
  /**
   * @return What is your animation?
   */
  public /*@ pure @*/ Animation animation(){
    return my_animation;
  }

  /**
   * @param the_animation This is your animation.
   */
  //@ ensures animation() == the_animation;
  public void animation(Animation the_animation){
    my_animation = the_animation;
  }

  /**
   * Take a next animation step.
   */
 public void animate(){
    
  }
  
  /**
   * @return How much damage have you sustained?
   */
  //@ ensures 0 <= \result & \result <= 20;
  public /*@ pure @*/ byte damage() {
    assert false; //@ assert false;
    return 0;
  }

  /**
   * @return What is your chimney?
   */
  public /*@ pure @*/ FactoryChimney chimney() {
    assert false; //@ assert false;
    return my_chimney;
  }

  /**
   * @return What is your sphere?
   */
  public /*@ pure @*/ FactorySphere sphere() {
    assert false; //@ assert false;
    return my_sphere;
  }

  /**
   * @param the_damage You have sustained this many units of damage.
   */
  //@ requires 0 <= the_damage;
  //@ ensures damage() == \old(damage() - the_damage);
  public void damage(byte the_damage) {
    assert false; //@ assert false;
  }
  
  /**
   * @return What is your attack behavior AI?
   */
  public /*@ pure @*/ AI attack(){
    return my_attack;
  }

  /**
   * @return What is your disturb behavior AI?
   */
  public /*@ pure @*/ AI disturb(){
    return my_disturb;
  }
  /**
   * @param the_behavior This is your attack behavior.
   */
  //@ ensures attack() == the_behavior;
  public void attack(AI the_behavior){
    
  }

  /**
   * @param the_behavior This is your disturb behavior.
   */
  //@ ensures disturb() == the_behavior;
  public void disturb(AI the_behavior){
    
  }
  /**
   * Simulate yourself for this many seconds.
   * @param some_seconds the number of seconds to simulate.
   */
  public void simulate(double time){
    my_physics.simulate(time);
  }
  /**
   * @return What is your acceleration in meters per second squared?
   */
  //@ ensures \result.length == 2;
  public /*@ pure @*/ double[] acceleration(){
   return my_physics.acceleration();
  }

  /**
   * @return What is the gravitational constant?
   */
  public /*@ pure @*/ double gravitational_constant(){
    return my_physics.gravitational_constant();
  }

  /**
   * @return What is your mass in kilograms?
   */
  //@ ensures 0 <= \result;
 public /*@ pure @*/ double mass(){

    return my_physics.mass();
  }

  /**
   * @return What is your momentum in kilograms*meters per second?
   */
  public /*@ pure @*/ double momentum(){
    return my_physics.momentum();
  }

  /**
   * @return What is your orientation in radians?
   */
  public /*@ pure @*/ double orientation(){
    return my_physics.orientation();
  }

  /**
   * @return What is your position in meters from the origin?
   */
  //@ ensures \result.length == 2;
 public  /*@ pure @*/ double[] position(){
   return my_physics.position();
  }

  /**
   * @return What is your velocity in meters per second?
   */
 public  /*@ pure @*/ double[] velocity(){
   return my_physics.velocity();
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
   * A chimney of a factory.
   * @author Joe Kiniry (kiniry@acm.org)
   * @version 18 April 2008
   */
  public class FactoryChimney extends StaticEntity
    implements EnemyEntity, Animatable {
   
    private Animation chimney_animation;
    private PhysicsClass chimney_physics;
    private final static double CHIMNEY_MASS = 2000;
    private boolean my_smoking_state;
    private final static double CHIMNEY_POS_X = 400;
    private final static double CHIMNEY_POS_Y = 200;
    
    public FactoryChimney(){
        chimney_physics = new PhysicsClass(CHIMNEY_POS_X, CHIMNEY_POS_Y, CHIMNEY_MASS);
        //my_animation = new Animation();
        my_smoking_state = true;
      }
      

    
    /**
     * @return Are you smoking?
     */
    public /*@ pure @*/ boolean smoking() {
      assert false; //@ assert false;
      return my_smoking_state;
    }

    /**
     * Your smoking state is dictated by this flag.
     * @param the_smoking_state A flag indicating whether the chimney
     * is smoking or not.
     */
    //@ ensures smoking() <==> the_smoking_state;
    public void smoking(boolean the_smoking_state) {
      assert false; //@ assert false;
    }
    
    /**
     * @return What is your attack behavior AI?
     */
    public /*@ pure @*/ AI attack(){
      return my_attack;
    }

    /**
     * @return What is your disturb behavior AI?
     */
    public /*@ pure @*/ AI disturb(){
      return my_disturb;
    }
    /**
     * @param the_behavior This is your attack behavior.
     */
    //@ ensures attack() == the_behavior;
    public void attack(AI the_behavior){
      
    }

    /**
     * @param the_behavior This is your disturb behavior.
     */
    //@ ensures disturb() == the_behavior;
    public void disturb(AI the_behavior){
      
    }
    
    /**
     * @return What is your animation?
     */
    public /*@ pure @*/ Animation animation(){
      return chimney_animation;
    }

    /**
     * @param the_animation This is your animation.
     */
    //@ ensures animation() == the_animation;
    public void animation(Animation the_animation){
      chimney_animation = the_animation;
    }

    /**
     * Take a next animation step.
     */
   public void animate(){
     
    }
    
    public void simulate(double time){
      chimney_physics.simulate(time);
    }
    /**
     * @return What is your acceleration in meters per second squared?
     */
    //@ ensures \result.length == 2;
    public /*@ pure @*/ double[] acceleration(){
     return chimney_physics.acceleration();
    }

    /**
     * @return What is the gravitational constant?
     */
    public /*@ pure @*/ double gravitational_constant(){
      return chimney_physics.gravitational_constant();
    }

    /**
     * @return What is your mass in kilograms?
     */
    //@ ensures 0 <= \result;
   public /*@ pure @*/ double mass(){

      return chimney_physics.mass();
    }

    /**
     * @return What is your momentum in kilograms*meters per second?
     */
    public /*@ pure @*/ double momentum(){
      return chimney_physics.momentum();
    }

    /**
     * @return What is your orientation in radians?
     */
    public /*@ pure @*/ double orientation(){
      return chimney_physics.orientation();
    }

    /**
     * @return What is your position in meters from the origin?
     */
    //@ ensures \result.length == 2;
   public  /*@ pure @*/ double[] position(){
     return chimney_physics.position();
    }

    /**
     * @return What is your velocity in meters per second?
     */
   public  /*@ pure @*/ double[] velocity(){
     return chimney_physics.velocity();
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
    
    private final static double FAC_SPHERE_MASS = 1000;
    private final static double FAC_SPHERE_POS_X = 400;
    private final static double FAC_SPHERE_POS_Y = 200;
    
    
    private PhysicsClass fac_sphere_physics;
    
    public FactorySphere(){
      fac_sphere_physics = new PhysicsClass(FAC_SPHERE_POS_X, FAC_SPHERE_POS_Y, FAC_SPHERE_MASS );
    }
    
  
    /**
     * Simulate yourself for this many seconds.
     * @param some_seconds the number of seconds to simulate.
     */
    public void simulate(double time){
      fac_sphere_physics.simulate(time);
    }
    /**
     * @return What is your acceleration in meters per second squared?
     */
    //@ ensures \result.length == 2;
    public /*@ pure @*/ double[] acceleration(){
     return fac_sphere_physics.acceleration();
    }

    /**
     * @return What is the gravitational constant?
     */
    public /*@ pure @*/ double gravitational_constant(){
      return fac_sphere_physics.gravitational_constant();
    }

    /**
     * @return What is your mass in kilograms?
     */
    //@ ensures 0 <= \result;
   public /*@ pure @*/ double mass(){

      return fac_sphere_physics.mass();
    }

    /**
     * @return What is your momentum in kilograms*meters per second?
     */
    public /*@ pure @*/ double momentum(){
      return fac_sphere_physics.momentum();
    }

    /**
     * @return What is your orientation in radians?
     */
    public /*@ pure @*/ double orientation(){
      return fac_sphere_physics.orientation();
    }

    /**
     * @return What is your position in meters from the origin?
     */
    //@ ensures \result.length == 2;
   public  /*@ pure @*/ double[] position(){
     return fac_sphere_physics.position();
    }

    /**
     * @return What is your velocity in meters per second?
     */
   public  /*@ pure @*/ double[] velocity(){
     return fac_sphere_physics.velocity();
    }
   
   /*@ public invariant (* A factory sphere's color is always green. *);
   @ public invariant color() == thrust.entities.properties.GameColor.GREEN;
   @ public invariant (* The goal sphere is not destroyed by a
   @                     factory's sphere. *);
   @*/
  }
}
