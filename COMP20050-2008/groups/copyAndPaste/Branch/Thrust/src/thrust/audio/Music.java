package thrust.audio;
import java.io.File;
import java.io.IOException;
import javax.sound.sampled.LineUnavailableException;
import javax.sound.sampled.UnsupportedAudioFileException;
import javax.sound.sampled.AudioFormat;
import javax.sound.sampled.AudioInputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.Clip;
import javax.sound.sampled.DataLine;
/**
 * Processes and delegates each keyboard input received.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 * @revised 25/04/08 Ciaran Flynn: 06516564 (wrote the code)
 * @revised 28/04/08 P Nevin (just fixed few style errors and added comments)
*/
public class Music {
  /**
   * create an instance of File, passing the wav file as argument.
   */
  private final transient File my_musicFile = new File("Thrust_music.wav.wav");
  /**
   * create an instance of Clip.
   */
  private final transient Clip my_music;
  /**
   * @throws LineUnavailableException
   * @throws IOException
   * @throws UnsupportedAudioFileException
   */
  public Music() throws LineUnavailableException, IOException, UnsupportedAudioFileException {
    final AudioInputStream my_Ais = AudioSystem.getAudioInputStream(my_musicFile);
    final AudioFormat af = my_Ais.getFormat();
    final DataLine.Info info = new DataLine.Info(Clip.class, af);
    my_music = (Clip) AudioSystem.getLine(info);
    my_music.open(my_Ais);
  }
  /**
   * @return whether the file is playing
   */
  public final boolean isPlaying() {
    return my_music.isRunning();
  }
  /**
   * start playing the music file.
   */
  public final void start() {
    my_music.loop(Clip.LOOP_CONTINUOUSLY);
  }
  /**
   * stop playing the music file.
   */
  public final void stop() {
    my_music.stop();
  }
}
