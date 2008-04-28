/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

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
 * In-game music.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class SoundEffect {
  // @ public model boolean is_playing;
  /**
   * In-game music. @ the clip @
   */
  private transient Clip my_clip;
  private final transient File my_soundFile = new File("Thrust_music.wav");

  /**
   * In-game music. @ the soundfile java.io input @
   * This is your sound effect.
   * @param the_sound_effect_file the sound effect to make.
   * @return the new sound effect for the effect stored in the provided file.
   */
  public SoundEffect(File my_soundFile)throws IOException , UnsupportedAudioFileException ,
  LineUnavailableException

  {
    final AudioInputStream my_sound =
          AudioSystem.getAudioInputStream(my_soundFile);
    final DataLine.Info info =
        new DataLine.Info(Clip.class, my_sound.getFormat());
    final Clip clip = (Clip) AudioSystem.getLine(info);
    clip.open(my_sound);

  }

  /**
   * Start playing the music.
   */
  // @ ensures is_playing;
  public final void start() {
    my_clip.loop(1);
  }
}
