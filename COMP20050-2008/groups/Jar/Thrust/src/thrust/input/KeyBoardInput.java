/**
 * 
 */
package thrust.input;

import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.util.logging.Logger;

import javax.swing.JFrame;
import javax.swing.*;
/**
 * @author Jar (jar@timbyr.com)
 * @version 30 April 2008
 *
 */
public class KeyBoardInput implements KeyListener {
  /** The number of keys that can be pressed */
  private static final int NO_KEYS = 256;
  /** Keyboard input logger. */
  Logger my_input_log = Logger.getLogger("Keyboard logger");
  /** Holds a boolean value which determines weather a key is down or not. */
  boolean[] keyStates = new boolean[NO_KEYS];
  /* (non-Javadoc)
   * @see java.awt.event.KeyListener#keyPressed(java.awt.event.KeyEvent)
   */
  /** Target for input. */
  final JFrame my_frame = new JFrame();
  public KeyBoardInput() {
    my_frame.setSize(0, 0);
    my_frame.setVisible(true);
    my_frame.addKeyListener(this);
  }

  public void keyPressed(final KeyEvent the_arg0) {
    // TODO Auto-generated method stub
    final int a = the_arg0.getKeyCode();
    final char b = the_arg0.getKeyChar();
    final String c = a + " " + b;
    my_input_log.info(c);
    keyStates[a] = true;
  }

  /* (non-Javadoc)
   * @see java.awt.event.KeyListener#keyReleased(java.awt.event.KeyEvent)
   */
  public void keyReleased(KeyEvent arg0) {
    keyStates[arg0.getKeyCode()] = false;
  }
  /*
   * 
   */
  public boolean keyDown(int keyNum){
    return keyStates[keyNum];
  }

  /* (non-Javadoc)
   * @see java.awt.event.KeyListener#keyTyped(java.awt.event.KeyEvent)
   */
  public void keyTyped(KeyEvent arg0) {
    // TODO Auto-generated method stub
    
  }
}
