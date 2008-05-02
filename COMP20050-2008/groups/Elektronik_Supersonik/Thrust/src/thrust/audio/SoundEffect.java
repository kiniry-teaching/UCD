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
import java.io.IOException;

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

  /**
   * The sound effect clip.
   */
  private transient Clip my_clip;

  /**
   * This is your sound effect.
   * @param the_sound_effect_file the sound effect to make.
   * @return the new sound effect for the effect stored in 's'.
   */
  public final/* @ pure @ */SoundEffect make(final File the_sound_effect_file) {
    AudioInputStream input_stream;
    DataLine.Info data_line_info;
    input_stream = null;
    try {
      input_stream = AudioSystem.getAudioInputStream(the_sound_effect_file);
    } catch (UnsupportedAudioFileException uafe) {
      uafe.printStackTrace(System.err);
    } catch (IOException ioe) {
      ioe.printStackTrace(System.err);
    }
    data_line_info = new DataLine.Info(Clip.class, input_stream.getFormat());
    try {
      my_clip = (Clip) AudioSystem.getLine(data_line_info);
      my_clip.open(input_stream);
    } catch (LineUnavailableException lue) {
      lue.printStackTrace(System.err);
    } catch (IOException ioe) {
      ioe.printStackTrace(System.err);
    }
    return this;
  }

  /**
   * Start playing your effect.
   */
  public final void start() {
    my_clip.loop(1);
  }
}
