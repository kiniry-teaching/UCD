/**
 *
 */
package thrust.input;

import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import javax.swing.JFrame;

/**
 * @author Jar (jar@timbyr.com)
 * @version 30 April 2008
 *
 */
public class KeyBoardInput implements KeyListener {
  /** The number of keys that can be pressed. */
  private static final int NO_KEYS = 256;
  /** The input handler. */
  private final transient InputHandler my_input = new InputHandler();
  /** Target for input. */
  private final transient JFrame my_frame = new JFrame();
  /** Holds a boolean value which determines weather a key is down or not. */
  private transient boolean[] my_keyStates = new boolean[NO_KEYS];
  /* (non-Javadoc)
   * @see java.awt.event.KeyListener#keyPressed(java.awt.event.KeyEvent)
   */
  public KeyBoardInput() {
    my_frame.setSize(0, 0);
    my_frame.setVisible(true);
    my_frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
    my_frame.addKeyListener(this);
  }

  public void keyPressed(final KeyEvent the_arg0) {
    if (the_arg0.getKeyCode() == KeyEvent.VK_SHIFT) {
      my_input.process((char)KeyEvent.VK_SHIFT);
    }
    if (my_input.legalInput(the_arg0.getKeyChar())) {
      my_input.process(the_arg0.getKeyChar());
    }
    my_keyStates[the_arg0.getKeyCode()] = true;
  }

  /* (non-Javadoc)
   * @see java.awt.event.KeyListener#keyReleased(java.awt.event.KeyEvent)
   */

  public void keyReleased(final KeyEvent the_arg0) {
    my_keyStates[the_arg0.getKeyCode()] = false;
  }

  /*
   *
   */
  public boolean keyDown(final int the_key_num) {
    return my_keyStates[the_key_num];
  }

  /* (non-Javadoc)
   * @see java.awt.event.KeyListener#keyTyped(java.awt.event.KeyEvent)
   */
  public void keyTyped(final KeyEvent the_arg0) {
    //@assert true;
  }
}
