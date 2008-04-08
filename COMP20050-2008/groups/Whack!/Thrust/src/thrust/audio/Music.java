package thrust.audio;

/**
 * In-game music.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
import java.io.File;

import javax.sound.sampled.AudioInputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.Clip;
import javax.sound.sampled.DataLine;
/**
 * 
 * @author Allison
 *
 */
public class Music extends Exception {
  
  //@ public model boolean is_playing;

  /**
   * 
   */
  private static final long serialVersionUID = 1L;
  /**
   * @return Is music playing?
   */
  //@ ensures \result == is_playing;
  /**
   * 
   */
  private Clip music;

  /**
   * 
   */
  public Music() {
    try {
      File musicFile = new File("/.../media/Thrustmusic.wav");
      AudioInputStream mus = AudioSystem.getAudioInputStream(musicFile);

      // load the sound into memory (a Clip)
      DataLine.Info info = new DataLine.Info(Clip.class, mus.getFormat());
      Clip clip = (Clip) AudioSystem.getLine(info);
      clip.open(mus);

    } catch (Exception e) {
      System.out.println("Error");
    }

  }
  
  

  /**
   *@return music.isRunning().; 
   */
  
  public final  /*@ pure @*/ boolean playing() {
    
    return music.isRunning();
    
  }

  /**
   * Start playing the music.
   */

  public final void start() {
    music.loop(Clip.LOOP_CONTINUOUSLY);
  }

  /**
   * Stop playing the music.
   */
  //@ ensures !is_playing;
  public final void stop() {
    music.stop();
  }
  
}
