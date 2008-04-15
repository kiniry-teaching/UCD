/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.display;

/**
 * Information about the game.
 *
 * @author Eoin Healy (eoin.healy@gmail.com)
 * @version 11 April 2008
 */
public abstract class AbstractInfoPanel {
  /**
   * @return Is the information panel currently displayed?
   */
  public abstract /*@ pure @*/ boolean displayed();

  /**
   * Display the information panel.
   */
  //@ ensures displayed();
  public abstract void display();

  /**
   * Hide the information panel.
   */
  //@ ensures !displayed();
  public abstract void hide();

  /**
   * Update the displayed information panel.
   */
  public abstract void update();
}
