package thrust.audio;

import javax.sound.sampled.AudioInputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.Clip;
import javax.sound.sampled.DataLine;
import javax.sound.sampled.LineUnavailableException;
import javax.sound.sampled.UnsupportedAudioFileException;

import java.io.File;
import java.io.IOException;



  /**
  * Any sound made in response to a event.
  * @author Stephen Walker (stephen.walker@ucdconnect.ie).
  * @version 8 April 2008
  */

public class SoundEffect {
  /**
   * This is your sound effect.
   * @param the_sound_effect_file the sound effect to make.
   * @return the new sound effect for the effect stored in 's'.
   *
   */
  private transient Clip my_clip;

  /**creating audio stream.*/
  private AudioInputStream my_stream;
  /*@ preparing to open music file from file system*/


  public final /*@ pure @*/ SoundEffect make(final File the_file) {
    try {
      my_stream = AudioSystem.getAudioInputStream(the_file);

      // specify what kind of line we want to create
      final DataLine.Info info =
        new DataLine.Info(Clip.class, my_stream.getFormat());
      // create the line
      my_clip = (Clip) AudioSystem.getLine(info);
      // load the samples from the stream
      my_clip.open(my_stream);
    } catch (LineUnavailableException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } catch (IOException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } catch (UnsupportedAudioFileException e1) {
      e1.printStackTrace();
    }
    final SoundEffect s = (SoundEffect) my_clip;
    return s;

  }


  /**
   * Start playing your effect.
   */
  public final void start() {
    my_clip.loop(1); //loop once as its only an effect
  }
}
