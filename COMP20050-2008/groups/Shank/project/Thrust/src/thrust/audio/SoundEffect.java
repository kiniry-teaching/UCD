package thrust.audio;

import java.io.File;
import javax.sound.sampled.Clip;
import javax.sound.sampled.AudioInputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.DataLine;
import javax.sound.sampled.FloatControl;
import javax.sound.sampled.LineUnavailableException;
import javax.sound.sampled.SourceDataLine;
import javax.sound.sampled.UnsupportedAudioFileException;
/**
 * Any sound made in response to a event.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 * Edited by Ben Fitzgerald on 07/04/2008
 */
public class SoundEffect
{
  /** The current sound clip that is in a the file.*/
  private Clip my_soundEffect;
  /**`Takes the clip and take the information inside the file.*/
  private AudioInputStream my_clipInStream;
  /**
   * This is your sound effect.
   * @param the_sound_effect_file the sound effect to make.
   * @return the new sound effect for the effect stored in 's'.
   */
  public /*@ pure @*/ SoundEffect make(final File the_sound_effect_file)
  {
    // File that contains a sound effect
    final File soundEffectFile = the_sound_effect_file;
    /** tried to use instead of try and catch
     * causes error
     * Count of 1 for 'LITERAL_ASSERT' descendant 'METHOD_CALL'
     * exceeds maximum count
     */
    //assert !soundEffectFile.exists();
    my_clipInStream = AudioSystem.getAudioInputStream(the_sound_effect_file);
    return null;
  }

  /**
   * Start playing your effect.
   */
  public void start() {
    my_soundEffect.loop(1);
  }
}