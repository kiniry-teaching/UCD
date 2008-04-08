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
public class Music {
  /**
   * The boolean that tells you whether music is playing.
   */
  //@ public model boolean is_playing;
  private transient boolean my_isplaying;

  /**
   * The in-game music clip.
   */
  private transient Clip my_clip;

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
    return my_isplaying;
  }

  /**
   * Start playing the music.
   */
  //@ ensures is_playing;
  public final void start() {
    my_clip.loop(Clip.LOOP_CONTINUOUSLY);
  }

  /**
   * Stop playing the music.
   */
  //@ ensures !is_playing;
  public final void stop() {
    my_clip.stop();
    my_clip.setMicrosecondPosition(0);
  }

  /**
   * Constructor helper method. Loads up the music file to a clip.
   */
  private void prepareMusicFile() {
    AudioInputStream input_stream;
    DataLine.Info data_line_info;
    final File music = new File("../../media/Thrust_music");
    input_stream = null;

    try {
      input_stream = AudioSystem.getAudioInputStream(music);
    } catch (UnsupportedAudioFileException uafe) {
      uafe.printStackTrace(System.err);
    } catch (IOException ioe) {
      ioe.printStackTrace(System.err);
    }

    data_line_info = new DataLine.Info(Clip.class, input_stream.getFormat());
    try {
      my_clip = (Clip) AudioSystem.getLine(data_line_info);
      my_clip.open(input_stream);
    } catch (LineUnavailableException lue) {
      lue.printStackTrace(System.err);
    } catch (IOException ioe) {
      ioe.printStackTrace(System.err);
    }
  }
}
