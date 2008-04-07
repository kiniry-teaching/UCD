package thrust.audio;

import java.io.File;
import javax.sound.sampled.*;





/**
 * Any sound made in response to a event.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class SoundEffect {
  /**
   * This is your sound effect.
   * @param the_sound_effect_file the sound effect to make.
   * @return the new sound effect for the effect stored in 's'.
   * 
   */
  private transient Clip clip;

  private AudioInputStream stream = null;
  /*@ preparing to open music file from file system*/

   
  public final /*@ pure @*/ SoundEffect make(final File sefile) {
    try {
      stream = AudioSystem.getAudioInputStream(sefile);

      
    } catch (Exception e) {
      e.fillInStackTrace();
    }
    // specify what kind of line we want to create 
    final DataLine.Info info = new DataLine.Info(Clip.class, stream.getFormat());
    
    try {
      // create the line
      clip = (Clip) AudioSystem.getLine(info);
      // load the samples from the stream 
      clip.open(stream);
      
    } catch (Exception e) {
      e.fillInStackTrace();
    }
    SoundEffect s = (SoundEffect) clip;
    return s;
  }
  

  /**
   * Start playing your effect.
   */
  public final void start() {
    clip.loop(1); //loop once as its only an effect
  }
}
