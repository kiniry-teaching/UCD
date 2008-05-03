package thrust.audio;

import java.io.File;
import java.io.IOException;
import java.util.logging.Logger;
import javax.sound.sampled.AudioInputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.Clip;
import javax.sound.sampled.DataLine;
import javax.sound.sampled.LineUnavailableException;
import javax.sound.sampled.UnsupportedAudioFileException;

/**
 * Any sound made in response to a event.
 * @author Keith Byrne, Eoghan O'Donovan, Sean Russell (Jar@timbyr.com).
 * @version 2 April 2008
 */
public class SoundEffect {
  /** Error log for Music class. */
  private static final Logger SOUNDLOG = Logger.getLogger("Error Log");
  /** Clip to be played. */
  private static Clip my_clip;
  /** Audio stream. */
  private static AudioInputStream audiois;

  /**
   * This is your sound effect.
   *
   * @param filename
   *          the sound effect to make.
   * @return the new sound effect for the effect stored in the provided file.
   */
  public /* @ pure @ */SoundEffect(final File the_filename) {
    setup(the_filename);
  }

  private void setup(final File the_filename) {
    // @ assert the_filename != null;
    try {
      audiois = AudioSystem.getAudioInputStream(the_filename);
      my_clip = (Clip) AudioSystem.getLine(new DataLine.Info(
                                       Clip.class, audiois.getFormat()));
      // @ assert my_clip !=null; my_clip.open(audiois);
    } catch (LineUnavailableException e) {
      SOUNDLOG.warning(e.getMessage());
    } catch (IOException e) {
      SOUNDLOG.warning(e.getMessage());
    } catch (UnsupportedAudioFileException e) {
      SOUNDLOG.warning(e.getMessage());
    }
  }
  /**
   * Start playing your effect.
   */
  public final void start() {
    my_clip.loop(1);
    // @ assert my_clip().isRunning();
  }
}
