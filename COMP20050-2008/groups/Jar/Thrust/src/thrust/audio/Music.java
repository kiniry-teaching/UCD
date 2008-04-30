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
 * In-game music.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class Music {
  // @ public model boolean is_playing;

  /** File for music. */
  private final transient File my_clipFile =
    new File("F:\\Jar\\Thrust\\media\\Thrust_music1.wav");
  /** Clip to be played. */
  // @ assert my_clipFile != null;
  private transient Clip my_clip;

  /** Constructor, sets up audio stream. */
  public Music() {
    AudioInputStream my_audiois = null;
    try {
      my_audiois = AudioSystem.getAudioInputStream(my_clipFile);
      my_clip = (Clip) AudioSystem.getLine(new DataLine.Info(
                              Clip.class, my_audiois.getFormat()));
      my_clip.open(my_audiois);
    } catch (UnsupportedAudioFileException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    } catch (LineUnavailableException e) {
      e.printStackTrace();
    }
  }

  /**
   * @return Is music playing?
   */
  // @ ensures \result == is_playing;
  public final/* @ pure @ */boolean playing() {
    // @ assert my_clip != null;
    return my_clip.isRunning();
  }

  /**
   * Start playing the music.
   */
  // @ ensures is_playing;
  public final void start() {
    // @ assert my_clip != null;
    my_clip.loop(Clip.LOOP_CONTINUOUSLY);
    // @ assert playing();
  }

  /**
   * Stop playing the music.
   */
  // @ ensures !is_playing;
  public final void stop() {
    my_clip.stop();
    my_clip.setMicrosecondPosition(0);
    // @ assert !playing();
  }
}
