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

import java.io.File;
import javax.media.bean.playerbean.MediaPlayer;

/**
 * Any sound made in response to a event.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class SoundEffect {
  /** The media player responsible for playing the sound effect. */
  private final transient /*@ non_null @*/ MediaPlayer my_media_player =
    new MediaPlayer();

  /**
   * This is your sound effect.
   * @param the_sound_effect_file the sound effect to make.
   * @return the new sound effect for the effect stored in the provided file.
   */
  public /*@ pure @*/ SoundEffect(final File the_sound_effect_file) {
    my_media_player.setMediaLocation(the_sound_effect_file.getAbsolutePath());
  }

  /** Start playing your effect. */
  public void start() {
    my_media_player.start();
  }
}
