ppackage thrust.audio;

import java.io.File;
import javax.sound.sampled.AudioFormat;
import javax.sound.sampled.AudioInputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.Clip;
import javax.sound.sampled.DataLine;

/**
 * Any sound made in response to a event.
 * 
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class SoundEffect {
  /** Clip to be played. */
  private Clip clip;
  /**
   * This is your sound effect.
   * 
   * @param filename
   *          the sound effect to make.
   * @return the new sound effect for the effect stored in 's'.
   */
  public final /* @ pure @ */ SoundEffect make(final File filename) {

    AudioInputStream audioInputStream = null;
    try {
      audioInputStream = AudioSystem.getAudioInputStream(filename);
    }
    catch (Exception e)
    {
      e.printStackTrace();
    }
    AudioFormat format = audioInputStream.getFormat();
    DataLine.Info info = new DataLine.Info(Clip.class, format);
    try
    {
      clip = (Clip) AudioSystem.getLine(info);
      clip.open(audioInputStream);
    }
    catch (Exception e)
    {
      e.printStackTrace();
    }
  return null;
  // @ assert false;
}

/**
 * Start playing your effect.
 */
public final void start() {
    clip.start();
  // @ assert false;
}
}
