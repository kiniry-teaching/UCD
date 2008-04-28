package thrust.entities;
   
   import thrust.entities.behaviors.AI;
   
   public class EnemyEntityIO implements EnemyEntity{
     /**
      * The bullet's/turret's disturb behavior.
      */
    private AI my_disturb;
    /**
     * The bullet's/turret's attack behavior.
     */
    private AI my_attack;
    
    public boolean Attack() {
      return true;
     
    }
  
    public AI attack() {
      return my_attack;
    }
  
    public void attack(AI behavior) {
      my_attack = behavior;
    }
 
    public AI disturb() {
      return my_disturb;
    }
  
    public void disturb(AI behavior) {
      my_disturb = behavior;
    }
  }