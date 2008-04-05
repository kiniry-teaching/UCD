package thrust.audio;

import java.io.File;
import javax.sound.sampled.AudioFormat;
import javax.sound.sampled.AudioInputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.DataLine;
import javax.sound.sampled.SourceDataLine;
import javax.sound.sampled.Clip;
/**
 * In-game music.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class Music {
  //@ public model boolean is_playing;
/**
 * Create new File for opening music file.
 */
  File my_music_file = new File("../../../media/Thrust_music.mp3");
  /**
   *  Create new clip for music.
   */
  Clip my_music;

  /**
   * Opens music file.
   */
  public Music() {
    AudioInputStream audio_stream = /*@ null */ null;
    try {
      audio_stream = AudioSystem.getAudioInputStream(my_music_file);
    }  catch (Exception e) {
      e.printStackTrace();
    }
    final AudioFormat aFormat = audio_stream.getFormat();
    final DataLine.Info info = new DataLine.Info(SourceDataLine.class, aFormat);
    try {
      my_music = (Clip) AudioSystem.getLine(info);
      my_music.open(audio_stream);
    } catch (Exception e) {
      e.printStackTrace();
    }
  }
  /**
   * @return Is music playing?
   */
  //@ ensures \result == is_playing;
  public /*@ pure @*/ boolean playing() {
    //@ assert music.isRunning() || !music.isRunning();
    return my_music.isRunning();
  }

  /**
   * Start playing the music.
   */
  //@ ensures is_playing;
  public void start() {
    //@ assert !playing();
    my_music.loop(Clip.LOOP_CONTINUOUSLY);
  }

  /**
   * Stop playing the music.
   */
  //@ ensures !is_playing;
  public void stop() {
    //@ assert playing();
    my_music.stop();
  }
}
