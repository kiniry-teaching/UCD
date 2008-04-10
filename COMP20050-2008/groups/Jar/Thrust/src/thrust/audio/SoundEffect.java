package thrust.audio;

import java.io.File;
import java.io.IOException;

import javax.sound.sampled.AudioFormat;
import javax.sound.sampled.AudioInputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.Clip;
import javax.sound.sampled.DataLine;
import javax.sound.sampled.LineUnavailableException;
import javax.sound.sampled.UnsupportedAudioFileException;

/**
 * Any sound made in response to a event.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class SoundEffect {
  /** Clip to be played. */
  private transient Clip my_clip;

  /**
   * This is your sound effect.
   *
   * @param filename
   *          the sound effect to make.
   * @return the new sound effect for the effect stored in 's'.
   */
  public final/* @ pure @ */SoundEffect make(final File the_filename) {

    AudioInputStream audiois = null;
    // @ assert the_filename != null;
    try {
      audiois = AudioSystem.getAudioInputStream(the_filename);
    } catch (UnsupportedAudioFileException e) {
      e.printStackTrace(System.err);
    } catch (IOException e) {
      e.printStackTrace(System.err);
    }

    final AudioFormat format = audiois.getFormat();
    final DataLine.Info info = new DataLine.Info(Clip.class, format);

    try {
      my_clip = (Clip) AudioSystem.getLine(info);
      // @ assert my_clip !=null;
      my_clip.open(audiois);
    } catch (LineUnavailableException e) {
      e.printStackTrace(System.err);
    } catch (IOException e) {
      e.printStackTrace(System.err);
    }

    return null;
    // @ assert false;
  }

  /**
   * Start playing your effect.
   */
  public final void start() {
    my_clip.loop(1);
    // @ assert my_clip().isRunning();
  }
}
