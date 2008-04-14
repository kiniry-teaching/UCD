package thrust.display;
/**
 * @author Tara Flood (0361188@ucdconnect.ie)
 * @version 14 April 2008
 */
public class AbstractInfoPanelWhack extends AbstractInfoPanel {
  /**
   * @return Is the information panel currently displayed?
   */
  public boolean displayed() {
    return true;
  }

  /**
   * Display the information panel.
   */
  //@ ensures displayed();
  public void display() {
  }

  /**
   * Hide the information panel.
   */
  //@ ensures !displayed();
  public void hide() {
  }

  /**
   * Update the displayed information panel.
   */
  public void update() {
  }

}
