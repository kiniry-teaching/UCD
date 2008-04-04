package thrust.audio;

import java.io.File;

/**
 * Any sound made in response to a event.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class SoundEffect {
  /**
   * This is your sound effect.
   * @param filename the sound effect to make.
   * @return the new sound effect for the effect stored in 's'.
   */
  public final /*@ pure @*/ SoundEffect make(final File filename) {
    //@ assert false;
    return null;
  }

  /**
   * Start playing your effect.
   */
  public final void start() {
    //@ assert false;
  }
}
