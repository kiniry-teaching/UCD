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
  public Clip clip;
  public AudioInputStream sound;
  /**
   * This is your sound effect.
   * @param the_sound_effect_file the sound effect to make.
   * @return the new sound effect for the effect stored in 's'.
   * @throws IOException 
   */
  public SoundEffect(final File the_sound_effect_file) throws IOException{
    try {
      sound = AudioSystem.getAudioInputStream(the_sound_effect_file);
    } catch (UnsupportedAudioFileException ex) { }
    DataLine.Info info = new DataLine.Info(Clip.class, sound.getFormat());
    try {
        clip = (Clip) AudioSystem.getLine(info);
        clip.open(sound);
     } catch (LineUnavailableException ex){}
  /**
   * Start playing your effect.
   */
  }
  public void start() {
    clip.start();
  }
}
