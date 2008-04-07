package thrust.audio;

import java.io.File;

import javax.sound.sampled.AudioInputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.Clip;
import javax.sound.sampled.DataLine;
/**
 * An example of loading and playing a sound using a Clip. This complete class
 * isn't in the book ;)
 */
public class SoundEffect extends Exception {
/**
 *
 */
  private static final long serialVersionUID = 1L;
  /**
   * 
   */
  private Clip bit;
  
  /** 
   * Set the value of Sound. 
   * @param SoundEffectfile. 
   */  
  public final/*@pure@*/ SoundEffect make(final File soundeffectfile) {
    // specify the sound to play
    // (assuming the sound can be played by the audio system)
    /**
     * @return SoundEffect.
     */
    
try {
  File soundeffectFile = new File("/media/Thrust.wav");
  AudioInputStream effect = AudioSystem.getAudioInputStream(soundeffectFile);

      // load the sound into memory (a Clip)
      DataLine.Info info = new DataLine.Info(Clip.class, effect.getFormat());
      Clip clip = (Clip) AudioSystem.getLine(info);
      clip.open(effect);
      return null;
      } catch (Exception e) {
      System.out.println("Error");
    }
      
      while (true) {
        bit.loop(Clip.LOOP_CONTINUOUSLY);
        }
      
  }
}        