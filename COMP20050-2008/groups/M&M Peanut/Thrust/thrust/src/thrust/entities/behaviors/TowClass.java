/**
 * @author Naomi O' Reilly
 * @version 18 April 2008
 */
package thrust.entities.behaviors;

public class TowClass implements Tow {
  //@ initially !towed();
  private boolean my_towed;
  //@assuming if !towed an entity is towing
  private boolean my_towing;

  public void tow() {
    if (!my_towed) {
      my_towing = true;
    } else {
      my_towed = true;
      my_towing = false;
    }

  }
  //@ ensures towed();
  public boolean towed() {
    my_towed = true;
  }

}