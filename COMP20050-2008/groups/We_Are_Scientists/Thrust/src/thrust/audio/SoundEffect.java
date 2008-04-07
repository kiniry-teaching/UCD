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
  public static void main(String[] args) throws Exception {

  File soundFile = new File("Thrust_music.wav");
  AudioInputStream sound = AudioSystem.getAudioInputStream(soundFile);

  DataLine.Info info = new DataLine.Info(Clip.class, sound.getFormat());
  Clip clip = (Clip) AudioSystem.getLine(info);
  clip.open(sound);
  }
  public /*@ pure @*/ SoundEffect make(File the_sound_effect_file) {
    assert false; //@ assert false;
    return null;
  }

  /**
   * Start playing your effect.
   */
  public void start() {
  
  }
}
