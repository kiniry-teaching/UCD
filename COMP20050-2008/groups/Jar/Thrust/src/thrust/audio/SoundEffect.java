package thrust.audio;

import javax.sound.sampled.AudioFormat;
import javax.sound.sampled.AudioInputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.DataLine;
import javax.sound.sampled.LineUnavailableException;
import javax.sound.sampled.SourceDataLine;
import javax.sound.sampled.UnsupportedAudioFileException;
import java.io.File;
import java.io.IOException;

/**
 * Any sound made in response to a event.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class SoundEffect {
  /** File for sound effects. */
   private File sound_effect;
  /**
   * This is your sound effect.
   * @param the_sound_effect_file the sound effect to make.
   * @return the new sound effect for the effect stored in 's'.
   */
  public final/*@ pure @*/ SoundEffect make(final File the_sound_effect_file) {
    sound_effect = the_sound_effect_file;
    assert false; //@ assert false;
    return null;
  }

  /**
   * Start playing your effect.
   */
  public final void start() {
    AudioInputStream audioInputStream = null;
    try {
      audioInputStream = AudioSystem.getAudioInputStream(sound_effect);
    } catch (UnsupportedAudioFileException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    }

    AudioFormat format = audioInputStream.getFormat();
    SourceDataLine auline = null;
    DataLine.Info info = new DataLine.Info(SourceDataLine.class, format);

    try {
      auline = (SourceDataLine) AudioSystem.getLine(info);
      auline.open(format);
    } catch (LineUnavailableException e) {
      e.printStackTrace();
      return;
    } catch (Exception e) {
      e.printStackTrace();
      return;
    }

    auline.start();
    assert false; //@ assert false;
  }
}
