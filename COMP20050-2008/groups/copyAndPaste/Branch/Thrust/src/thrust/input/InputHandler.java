 package thrust.input; 
 import java.awt.event.KeyEvent; 
  
 /** 
  * Processes and delegates each keyboard input received. 
  * @author  Ciaran Flynn
  * @version  10 April 2008 
  */  
 public class InputHandler { 
  
  
   /** Display the high scores*/ 
   public static final char DISPLAY_HIGH_SCORES = 104; 
   /** Toggle music or sound effects. */ 
   public static final char TOGGLE_MUSIC_OR_EFFECTS = 109; 
   /** Start the game. */ 
   public static final char START_GAME = 115; 
   /** Stop the game. */ 
   public static final char STOP_GAME = 27; 
   /** Fire the gun. */ 
   public static final char FIRE_GUN = 12; 
  /** Turn left. */ 
   public static final char TURN_LEFT = 97; 
   /** Turn right. */ 
   public static final char TURN_RIGHT = 100; 
   /** Use engine. */ 
   public static final char USE_ENGINE = 15; 
   /** Use shield. */ 
   public static final char USE_SHIELD = 32; 
  
  
   
   public final char[] legal_inputs() { 
      
     final char[] legal_inputs = {DISPLAY_HIGH_SCORES, TOGGLE_MUSIC_OR_EFFECTS, 
                                  START_GAME, STOP_GAME, FIRE_GUN, TURN_LEFT, 
                                  TURN_RIGHT, USE_ENGINE, USE_SHIELD }; 
     return legal_inputs; 
   } 
  
   /** 
    * @return Is this character a legal keyboard input? 
    * @param the_character the character to check. 
    */ 
   /*@ ensures \result <==> (the_character == DISPLAY_HIGH_SCORES) | 
     @                      (the_character == TOGGLE_MUSIC_OR_EFFECTS) | 
     @                      (the_character == START_GAME) | 
     @                      (the_character == STOP_GAME) | 
     @                      (the_character == FIRE_GUN) | 
     @                      (the_character == TURN_LEFT) | 
     @                      (the_character == TURN_RIGHT) | 
     @                      (the_character == USE_ENGINE) | 
     @                      (the_character == USE_SHIELD); 
     @*/ 
   
  
   
   public void process(final char the_keyboard_input) { 
     assert false; //@ assert false 
     switch (the_keyboard_input) { 
       case DISPLAY_HIGH_SCORES: 
         System.out.print("High scores method"); 
         break; 
       case TOGGLE_MUSIC_OR_EFFECTS: 
         System.out.print("Trigger Music method"); 
         break; 
       case START_GAME: 
         System.out.print("Begin the game"); 
         break; 
       case STOP_GAME: 
         System.out.print("End the game"); 
         break; 
       case FIRE_GUN: 
        System.out.print("Fire bullet"); 
        break; 
      case TURN_LEFT: 
        System.out.print("Turn left"); 
        break; 
      case TURN_RIGHT: 
        System.out.print("Turn right"); 
        break; 
      case USE_ENGINE: 
        System.out.print("thrust"); 
        break; 
      case USE_SHIELD: 
        System.out.print("Shield on"); 
         break; 
       default: 
     
     } 
   } 
 } 
