package thrust.audio;
import java.io.*;
import sun.audio.*;

/**
 * Any sound made in response to a event.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class SoundEffect {
  private AudioStream run;
  /**
   * This is your sound effect.
   * @param the_sound_effect_file the sound effect to make.
   * @return the new sound effect for the effect stored in 's'.
   */
  public SoundEffect(final String My_file) {
    try {
      final InputStream input = new FileInputStream(My_file);
      run = new AudioStream(input);
    } catch (IOException ex) {
      ex.printStackTrace();
    }
  /**
   * Start playing your effect.
   */
  }
  public void start() {
    AudioPlayer.player.start(run);
  }
  public static void main(String[] args){
    SoundEffect s = new SoundEffect("./media/Thrust_music.wav");
    s.start();
  }
}
