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
 * An example of loading and playing a sound using a Clip. This complete class
 * isn't in the book ;)
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class SoundEffect extends Exception {
  /**
   *
   */
  private static final long serialVersionUID = 1L;
  /**
   *
   */
  private Clip my_bit;

  /**
   *@return SoundEffect.;
   *@param soundfile inputs a sound.;
   */
  public final/*@pure@*/ SoundEffect  make(final File the_soundfile) {
    // specify the sound to play
    // (assuming the sound can be played by the audio system)

    final File soundFile = new File("/.../media/Thrust.wav");

    try {
      final AudioInputStream effect;
      effect = AudioSystem.getAudioInputStream(soundFile);
      final DataLine.Info info;
      info = new DataLine.Info(Clip.class, effect.getFormat());
      Clip clip;
      try {
        clip = (Clip) AudioSystem.getLine(info);
        try {
          clip.open(effect);
        } catch (IOException e) {
          e.printStackTrace();
        }
      } catch (LineUnavailableException e) {

        e.printStackTrace();
      }
    } catch (UnsupportedAudioFileException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } catch (IOException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    final SoundEffect sou = (SoundEffect) my_bit;
    return sou;
    // load the sound into memory (a Clip)
  }
  public final void start() {
    my_bit.loop(Clip.LOOP_CONTINUOUSLY);


  }
}
