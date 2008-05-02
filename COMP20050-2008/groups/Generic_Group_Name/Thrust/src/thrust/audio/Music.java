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
import sun.audio.*;    //import the sun.audio package
import java.io.*;

public class Music {
  //@ public model boolean is_playing;
  
  boolean playing;
try {
  public InputStream in = new FileInputStream("Thrust_music.mp3");
  public AudioStream as = new AudioStream(in); 
  public AudioData data = as.getData();
  public ContinuousAudioDataStream cas = new ContinuousAudioDataStream(data);
  /**
   * @return Is music playing?
   */
  //@ ensures \result == is_playing;
  public boolean playing() {
    return playing;
  }

  /**
   * Start playing the music.
   */
  //@ ensures is_playing;
  public void start() {
    AudioPlayer.player.start(cas);
    playing = true;
  }

  /**
   * Stop playing the music.
   */
  //@ ensures !is_playing;
  public void stop() {
    AudioPlayer.player.stop(cas);
    playing = false;
  }
} catch (Exception e) {}

}
