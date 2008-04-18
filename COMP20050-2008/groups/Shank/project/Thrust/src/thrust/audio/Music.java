package thrust.audio;
import java.io.File;
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
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class Music {
  //@ public model boolean is_playing;

  /**
   * @return Is music playing?
   */
  //@ ensures \result == is_playing;
  public /*@ pure @*/ boolean playing() {
    assert false; //@ assert false;
    return false;
  }
  
  public void openMusic() {
    
    final File Music_File = new File("");
    AudioInputStream game_audio_stream = null;
    Clip clip;
    
    try {
      game_audio_stream = AudioSystem.getAudioInputStream(Music_File);
      
    } catch (UnsupportedAudioFileException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    }
    
    final DataLine.Info info =
      new DataLine.Info(SourceDataLine.class, my_audio_stream.getFormat());
      try {
        clip = (Clip) AudioSystem.getLine(info);
        clip.open(game_audio_stream);
      } catch (IOException e) {
        e.printStackTrace();
      } catch (LineUnavailableException e) {
        e.printStackTrace();
      }
  }  
    
  /**
   * Start playing the music.
   */
  //@ ensures is_playing;
  public void start() {
    assert false; //@ assert false;
  }

  /**
   * Stop playing the music.
   */
  //@ ensures !is_playing;
  public void stop() {
    assert false; //@ assert false;
  }
}
