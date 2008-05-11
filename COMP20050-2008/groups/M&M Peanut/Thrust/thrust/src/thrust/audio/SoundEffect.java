/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */


package thrust.audio;

import java.io.File;
import javax.sound.sampled.*;

/**
 * Any sound made in response to a event.
 * @author Joe Kiniry (kiniry@acm.org)
 * @revised Sean Jago
 *         
 * @version 11 April 2008
 */

public class SoundEffect 
{
  /**
   * Your sound effect is 's'.
   * @param s the sound effect to make.
   */
   private Clip effect;
   private AudioInputStream file_in;

  public /*@ pure @*/ SoundEffect make(File s) 
  {
    file_in = AudioInputStream();
    Dataline.Info Clip = new Dataline.Info(Clip.class, file_in.getFormat());
    effect = (Clip) AudioSystem.getLine (info);
    effect.open (file_in);
  }

  /**
   * Start playing your effect.
   */
  public void start() 
  {
    effect.start();
  }
}