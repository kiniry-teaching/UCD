package thrust.entities.behaviors;
/**
 * @author Tara Flood (Tara.Flood@ucdconnect.ie)
 * @version 23 April 2008
 */
public class Towwhack {
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
