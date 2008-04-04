package thrust.audio;

import java.io.File;
import javax.sound.sampled.*;

/**
 * Any sound made in response to a event.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class SoundEffect {
  private Clip sound = null;
  /**
   * This is your sound effect.
   * @param the_sound_effect_file the sound effect to make.
   * @return the new sound effect for the effect stored in 's'.
   */
  public /*@ pure @*/ SoundEffect(File the_sound_effect_file) {
     AudioInputStream audioStream = null;
    
    try{
      audioStream = AudioSystem.getAudioInputStream(the_sound_effect_file);
    }  catch (Exception e){
      e.printStackTrace();
    }

    final AudioFormat aFormat = audioStream.getFormat();
    final DataLine.Info info = new DataLine.Info(SourceDataLine.class, aFormat);
    
    try {
      sound = (Clip) AudioSystem.getLine(info);
      sound.open(audioStream);
    }catch (Exception e){
      e.printStackTrace();
    }
  }

  /**
   * Start playing your effect.
   */
  public void start() {
    sound.loop(1);
    assert false; //@ assert false;
  }
}
