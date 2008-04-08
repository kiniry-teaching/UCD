package thrust.audio;

import java.io.File;
import javax.sound.sampled.*;
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
  public /*@ pure @*/ SoundEffect make(File the_sound_effect_file) {
	
	private TargetDataLine s_f;
	private AudioInputStream s_f_x;
	DataLine.Info data = new DataLine.Info(TargetDataLine.class, audioFormat);
	
	.getAudioInputStream(.wav, the_sound_effect_file);
	  
	assert false; //@ assert false;
    return null;
  }

  /**
   * Start playing your effect.
   */
  public void start() {
    assert false; //@ assert false;
  }
}
