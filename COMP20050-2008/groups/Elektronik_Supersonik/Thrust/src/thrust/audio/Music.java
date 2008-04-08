package thrust.audio;

import javax.sound.sampled.AudioInputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.Clip;
import javax.sound.sampled.DataLine;
import java.io.File;

/**
 * In-game music.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class Music {
  /**
   * The boolean that tells you whether music is playing.
   */
  //@ public model boolean is_playing;
  private boolean playing;
  
  /**
   * The in-game music clip.
   */
  private Clip theClip;
  
  /**
   * Constructor method. Creates theClip.
   */
  public Music() {
    prepareMusicFile();
  }
  
  /**
   * @return Is music playing?
   */
  //@ ensures \result == is_playing;
  public final /*@ pure @*/ boolean playing() {
    return playing;
  }

  /**
   * Start playing the music.
   */
  //@ ensures is_playing;
  public final void start() {
    theClip.loop(Clip.LOOP_CONTINUOUSLY);
  }

  /**
   * Stop playing the music.
   */
  //@ ensures !is_playing;
  public final void stop() {
    theClip.stop();
    theClip.setMicrosecondPosition(0);
  }
  
  /**
   * Constructor helper method. Loads up the music file to a clip.
   */
  private void prepareMusicFile() {
    AudioInputStream inputStream;
    DataLine.Info dataLineInfo;
    File music = new File("../../media/Thrust_music");
    inputStream = null;
    try {
      inputStream = AudioSystem.getAudioInputStream(music);
    } catch (Exception e) {
      e.printStackTrace(System.err);
    }
    dataLineInfo = new DataLine.Info(Clip.class, inputStream.getFormat());
    try {
      theClip = (Clip) AudioSystem.getLine(dataLineInfo);
      theClip.open(inputStream);
    } catch (Exception e) {
      e.printStackTrace(System.err);
    }
  }
}
