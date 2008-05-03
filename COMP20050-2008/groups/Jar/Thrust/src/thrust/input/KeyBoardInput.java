/**
 *
 */
package thrust.input;

import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import javax.swing.JFrame;

import thrust.entities.about.GameState;

/**
 * @author Jar (jar@timbyr.com)
 * @version 30 April 2008
 *
 */
public class KeyBoardInput implements KeyListener {
  /** The input handler. */
  public static final InputHandler INPUT = new InputHandler();
  /** Target for input. */
  private static final JFrame FRAME = new JFrame();

  /* (non-Javadoc)
   * @see java.awt.event.KeyListener#keyPressed(java.awt.event.KeyEvent)
   */
  public KeyBoardInput() {
    FRAME.setSize(0, 0);
    FRAME.setVisible(true);
    FRAME.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
    FRAME.addKeyListener(this);
  }

  public void keyPressed(final KeyEvent the_arg0) {
    if (the_arg0.getKeyCode() == KeyEvent.VK_SHIFT) {
      INPUT.process((char)KeyEvent.VK_SHIFT);
    }
    if (INPUT.legalInput(the_arg0.getKeyChar())) {
      INPUT.process(the_arg0.getKeyChar());
    }
  }

  /* (non-Javadoc)
   * @see java.awt.event.KeyListener#keyReleased(java.awt.event.KeyEvent)
   */

  public void keyReleased(final KeyEvent the_arg0) {
    if (thrust.Main.GAMESTATE.get_state() == GameState.PLAY) {
      if (the_arg0.getKeyCode() == KeyEvent.VK_SHIFT) {
        INPUT.processReleased((char)KeyEvent.VK_SHIFT);
      }
      if (INPUT.legalInput(the_arg0.getKeyChar())) {
        INPUT.processReleased(the_arg0.getKeyChar());
      }
    }
  }

  /* (non-Javadoc)
   * @see java.awt.event.KeyListener#keyTyped(java.awt.event.KeyEvent)
   */
  public void keyTyped(final KeyEvent the_arg0) {
    //@assert true;
  }
}
