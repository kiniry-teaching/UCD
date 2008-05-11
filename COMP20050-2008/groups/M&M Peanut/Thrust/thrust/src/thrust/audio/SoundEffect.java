

package thrust.audio;

import java.io.File;
import javax.sound.sampled.*;

public class SoundEffect 
{
  /**
   * Your sound effect is 's'.
   * @param s the sound effect to make.
   */
   private Clip effect;
   private AudioInputStream file_in;

  public /*@ pure @*/ SoundEffect make(File "Thrust.wav.wav") 
  {
      file_in = AudioInputStream("Thrust.wav.wav");
    Dataline.Info Clip = new Dataline.Info(Clip.class, file_in.getFormat());
    effect = (Clip) AudioSystem.getLine (info);
    effect.open (file_in);
  }

  /**
   * Start playing your effect.
   */
  public void start() 
  {
    effect.start();
  }
}