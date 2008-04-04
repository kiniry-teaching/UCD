package thrust.audio;
import javax.sound.sampled.*;
/**
 * In-game music.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class Music {
  //@ public model boolean is_playing;

  
  
  
  
  boolean is_playing;
  /**
   * @return Is music playing?
   */
  //@ ensures \result == is_playing;
  public /*@ pure @*/ boolean playing() {
    try {
      // From file
      AudioInputStream stream = AudioSystem.getAudioInputStream(new File("thrust"));
  
     
  
      // At present, ALAW and ULAW encodings must be converted
      // to PCM_SIGNED before it can be played
      AudioFormat format = stream.getFormat();
      if (format.getEncoding() != AudioFormat.Encoding.PCM_SIGNED) {
          format = new AudioFormat(
                  AudioFormat.Encoding.PCM_SIGNED,
                  format.getSampleRate(),
                  format.getSampleSizeInBits()*2,
                  format.getChannels(),
                  format.getFrameSize()*2,
                  format.getFrameRate(),
                  true);        // big endian
          stream = AudioSystem.getAudioInputStream(format, stream);
      }
  
      // Create the clip
      DataLine.Info info = new DataLine.Info(
          Clip.class, stream.getFormat(), ((int)stream.getFrameLength()*format.getFrameSize()));
      Clip clip = (Clip) AudioSystem.getLine(info);
  
      // This method does not return until the audio file is completely loaded
      clip.open(stream);
  
      // Start playing
      clip.start();
  } catch (MalformedURLException e) {
  } catch (IOException e) {
  } catch (LineUnavailableException e) {
  } catch (UnsupportedAudioFileException e) {
  }
  }

  /**
   * Start playing the music.
   */
  //@ ensures is_playing;
  public void start() {
    //clip.start();
    clip.loop(Clip.LOOP_CONTINUOUSLY);
    int numberOfPlays = 3;
    //clip.loop(numberOfPlays-1);
  }

  /**
   * Stop playing the music.
   */
  //@ ensures !is_playing;
  public void stop() {
    assert false; //@ assert false;
  }
}
