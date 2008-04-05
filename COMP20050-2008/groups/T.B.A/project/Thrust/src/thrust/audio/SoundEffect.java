package thrust.audio;

import java.io.File;
import javax.sound.sampled.AudioFormat;
import javax.sound.sampled.AudioInputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.DataLine;
import javax.sound.sampled.SourceDataLine;
import javax.sound.sampled.Clip;

/**
 * Any sound made in response to a event.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class SoundEffect {
  /**
   * Clip for playing sound effect.
   */
  private Clip my_sound;
  /**
   * This is your sound effect.
   * @param the_sound_effect_file the sound effect to make.
   * @return the new sound effect for the effect stored in 's'.
   */
  public /*@ pure @*/ SoundEffect(final File the_sound_effect_file) {
    AudioInputStream audio_stream = /*@ null */ null;
    try {
      audio_stream = AudioSystem.getAudioInputStream(the_sound_effect_file);
    }  catch (Exception e) {
      e.printStackTrace();
    }
    final AudioFormat aFormat = audio_stream.getFormat();
    final DataLine.Info info = new DataLine.Info(SourceDataLine.class, aFormat);
    try {
      my_sound = (Clip) AudioSystem.getLine(info);
      my_sound.open(audio_stream);
    } catch (Exception e) {
      e.printStackTrace();
    }
  }
  /**
   * Start playing your effect.
   */
  public void start() {
    my_sound.loop(1); /* play file once */
  }
}
