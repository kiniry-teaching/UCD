/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.input;

import java.applet.Applet;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
//import java.util.logging.ConsoleHandler;
import java.util.logging.Logger;

/**
 * An applet used to test classes in the thrust.input package.
 * We use an applet so that we can immediately consume keyboard events
 * with a KeyListener.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 23 April 2008
 */
public class InputHandlerTestApplet extends Applet implements KeyListener {
  /** The default serialVersionUID. */
  private static final long serialVersionUID = 1L;

  /** Logger for this test class. */
  private static final Logger LOGGER =
    Logger.getLogger("InputHandlerTestApplet");

  /** The input handler related to this test applet. */
  private transient InputHandler my_input_handler;

  /** {@inheritDoc} */
  public void init() {
    LOGGER.info("InputHandlerTestApplet started.");
    my_input_handler = new InputHandler();
    this.addKeyListener(this);
  }

  /** {@inheritDoc} */
  public void keyPressed(final KeyEvent the_event) {
    final int an_input = (char)the_event.getKeyCode();
    if (my_input_handler.legal_input((char)an_input)) {
      LOGGER.info("legal input: '" +
                  KeyEvent.getKeyText(an_input) + "'");
      my_input_handler.process((char)an_input);
    } else {
      LOGGER.info("bad input: '" + KeyEvent.getKeyText(an_input) + "'");
    }
    if (an_input == InputHandler.STOP_GAME) {
      System.exit(0);
    }
    LOGGER.exiting("InputHandler", "main");
  }

  /** {@inheritDoc} */
  public void keyReleased(final KeyEvent the_event) {
    // skip
  }

  /** {@inheritDoc} */
  public void keyTyped(final KeyEvent the_event) {
    // skip
  }
}
