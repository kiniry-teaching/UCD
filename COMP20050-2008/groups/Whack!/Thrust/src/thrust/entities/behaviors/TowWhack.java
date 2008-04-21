package thrust.entities.behaviors;
/**
 * An entity that is a threat to the spaceship.
 * @author Tara Flood (Tara.Flood@ucdconnect.ie)
 * @version 21 April 2008
 */
public class TowWhack implements Tow {
//@ initially !towed();

  /**
   * @return Are you currently towing or being towed?
   */
  public/*@ pure @*/ boolean towed() {
    return false;
  }

  /**
   * You are now towing or being towed.
   */
  //@ ensures towed();
  public void tow() {

  }

}
