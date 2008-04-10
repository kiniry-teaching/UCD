package thrust.audio;

import java.io.File;
import java.io.IOException;

import javax.sound.sampled.AudioFormat;
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
          new File("../../../media/Thrust_music.wav");
  /** Clip to be played. */
  // @ assert my_clipFile != null;
  private final transient Clip my_clip;

  /** Constructor, sets up audio stream. */
  public Music() throws LineUnavailableException, IOException,
      UnsupportedAudioFileException {
    final AudioInputStream audiois =
          AudioSystem.getAudioInputStream(my_clipFile);
    final AudioFormat format = audiois.getFormat();
    final DataLine.Info info = new DataLine.Info(Clip.class, format);
    my_clip = (Clip) AudioSystem.getLine(info);
 // @ assert my_clip != null;
    my_clip.open(audiois);
  }

  /**
   * @return Is music playing?
   */
  // @ ensures \result == is_playing;
  public final/* @ pure @ */boolean playing() {
    return my_clip.isRunning();
    // @ assert true;
  }

  /**
   * Start playing the music.
   */
  // @ ensures is_playing;
  public final void start() {
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
