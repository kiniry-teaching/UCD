package thrust.audio;

import java.io.File;
import javax.sound.sampled.AudioFormat;
import javax.sound.sampled.AudioInputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.Clip;
import javax.sound.sampled.DataLine;

/**
 * In-game music.
 * 
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class Music {
  // @ public model boolean is_playing;

  /** File for music. */
  private File clipFile = new File("/home/keith/1.WAV");
  /** Clip to be played. */
  private Clip clip;
  
  /** Constructor, sets up audio stream. */
  public Music() {
    AudioInputStream audioInputStream = null;
    try {
      audioInputStream = AudioSystem.getAudioInputStream(clipFile);
    } catch (Exception e) {
      e.printStackTrace();
    }
    AudioFormat format = audioInputStream.getFormat();
    DataLine.Info info = new DataLine.Info(Clip.class, format);
    try {
      clip = (Clip) AudioSystem.getLine(info);
      clip.open(audioInputStream);
    } catch (Exception e) {
      e.printStackTrace();
    }

  }

  /**
   * @return Is music playing?
   */
  // @ ensures \result == is_playing;
  public final/* @ pure @ */boolean playing() {
    return clip.isRunning();
    // @ assert false;
  }

  /**
   * Start playing the music.
   */
  // @ ensures is_playing;
  public final void start() {
    clip.loop(Clip.LOOP_CONTINUOUSLY);
    // @ assert false;

  }

  /**
   * Stop playing the music.
   */
  // @ ensures !is_playing;
  public final void stop() {
    clip.stop();
    clip.setMicrosecondPosition(0);
    // @ assert false;
  }
}
