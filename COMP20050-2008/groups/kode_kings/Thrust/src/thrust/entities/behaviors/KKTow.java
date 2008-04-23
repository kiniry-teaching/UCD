/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Colin Casey (colin.casey@org.com)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "April 2008"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */
package thrust.entities.behaviors;
/**
 * An entity that is a threat to the spaceship.
 * @author Ciaran Hale (ciaran.hale@ucd.connect.ie)
 * @author Colin Casey (colin.casey@org.com)
 * @version 23 April 2008
 */

public class KKTow implements Tow {

  /** Tow status of entity. */
  private boolean my_tow_indicator;

  public boolean towed() {
    return my_tow_indicator;
  }

  public void tow() {
    my_tow_indicator = true;
  }
}
