package thrust.audio;

import java.io.File;
import javax.sound.sampled.AudioInputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.Clip;
import javax.sound.sampled.DataLine;

/**
 * Any sound made in response to a event.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class SoundEffect {

  /**
   * The sound effect clip.
   */
  private Clip theClip;
  /**
   * This is your sound effect.
   * @param the_sound_effect_file the sound effect to make.
   * @return the new sound effect for the effect stored in 's'.
   */
  public final /*@ pure @*/ SoundEffect make(final File the_sound_effect_file) {
    AudioInputStream inputStream;
    DataLine.Info dataLineInfo;
    inputStream = null;
    try {
      inputStream = AudioSystem.getAudioInputStream(the_sound_effect_file);
    } catch (Exception e) {
      e.printStackTrace(System.err);
    }
    dataLineInfo = new DataLine.Info(Clip.class, inputStream.getFormat());
    try {
      theClip = (Clip) AudioSystem.getLine(dataLineInfo);
      theClip.open(inputStream);
    } catch (Exception e) {
      e.printStackTrace(System.err);
    }
    return this;
  }

  /**
   * Start playing your effect.
   */
  public final void start() {
    theClip.loop(1);
  }
}
