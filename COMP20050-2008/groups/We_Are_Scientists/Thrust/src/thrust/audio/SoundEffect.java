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
   * This is your sound effect.
   * @param the_sound_effect_file the sound effect to make.
   * @return the new sound effect for the effect stored in 's'.
   */
  //public static void main(String[] args) throws Exception {
  private  Clip my_clip;
  /**
   * Any sound made in response to a event.
   * @author simon
   * @param  soundFile sound file
   */
  public final/* @ pure @ */SoundEffect make(final File the_sound) throws
  IOException ,
  UnsupportedAudioFileException ,
  LineUnavailableException {

    AudioInputStream sound = null;


    sound = AudioSystem.getAudioInputStream(the_sound);

          //final AudioFormat format = audioInputStream.getFormat();
    final DataLine.Info info =
            new DataLine.Info(Clip.class, sound.getFormat());
    my_clip = (Clip) AudioSystem.getLine(info);
    my_clip.open(sound);
    return null;
  }


  /**
   * Start playing your effect.
   */

  public final void start() {
    my_clip.start();
  }
}
