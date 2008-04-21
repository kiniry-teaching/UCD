package thrust.display;

/**
 * Top scores of past players.
 *
 * @author Siobhan Dunne (Siobhan.Dunne@ucd.ie)
 * @version 14 April 2008
 */

public class InfoPanel extends AbstractInfoPanel {

  /**
   *  Is the information panel currently displayed?
   */
  private boolean my_display;

  /**
   * @return Is the information panel currently displayed?
   */
  public /*@ pure @*/ boolean displayed() {
    return my_display;
  }

  /**
   * Display the information panel.
   */
  //@ ensures displayed();
  public void display() {
    if (!displayed()) {
      System.out.print("display");
      my_display = true;
      //display
    }
  }

  /**
   * Hide the information panel.
   */
  //@ ensures !displayed();
  public void hide() {
    if (displayed()) {
      System.out.print("hide");
      my_display = false;
    }
  }

  /**
   * Update the displayed information panel.
   */
  public void update() {

    //update
  }

}
