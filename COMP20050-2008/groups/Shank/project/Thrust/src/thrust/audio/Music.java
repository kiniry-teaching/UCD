package thrust.audio;
import java.io.File;
import javax.sound.sampled.AudioInputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.DataLine;
import javax.sound.sampled.SourceDataLine;
import javax.sound.sampled.Clip;
import java.io.IOException;
import javax.sound.sampled.UnsupportedAudioFileException;
import javax.sound.sampled.LineUnavailableException;
/**
 * In-game music.
 * @author Roger Thomas (roger.thomas@ucdconnect.ie)
 * @version 2 April 2008
 * Implpemented friday 18 April 2008
 */
public class Music {
  //@ public model boolean is_playing;
  /**
   * @return music clip
   */
  private Clip my_clip;

  /**
   * @return Is music playing?
   */
  //@ ensures \result == is_playing;
  public void openMusic() {
    final File music_file = new File("");
    AudioInputStream game_audio_stream = null;
    try {
      game_audio_stream = AudioSystem.getAudioInputStream(music_file);
    } catch (UnsupportedAudioFileException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    }
    final DataLine.Info info =
      new DataLine.Info(SourceDataLine.class, game_audio_stream.getFormat());
    try {
      my_clip = (Clip)AudioSystem.getLine(info);
      my_clip.open(game_audio_stream);
    } catch (IOException e) {
      e.printStackTrace();
    } catch (LineUnavailableException e)
    {
      e.printStackTrace();
    }
  }

  public /*@ pure @*/ boolean playing() {
    //assert false; //@ assert false;
    return my_clip.isRunning();
  }

  /**
   * Start playing the music.
   */
  //@ ensures is_playing;
  public void start() {
    my_clip.loop(Clip.LOOP_CONTINUOUSLY);
  }

  /**
   * Stop playing the music.
   */
  //@ ensures !is_playing;
  public void stop() {
    my_clip.stop();
  }
}
