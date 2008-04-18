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
public class SoundEffect {
  //@ public model boolean is_playing;
  /**
   * @return music clip
   */
  private Clip my_sound_effect;


  //@ ensures \result == my_sound_effect_is_playing;
  public SoundEffect play(final File the_sound_file) {
    //final File music_clip = new Clip;
    AudioInputStream game_audio_stream = null;
    try {
      game_audio_stream = AudioSystem.getAudioInputStream(the_sound_file);
    } catch (UnsupportedAudioFileException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    }
    final DataLine.Info info =
      new DataLine.Info(SourceDataLine.class, game_audio_stream.getFormat());
    try {
      my_sound_effect = (Clip)AudioSystem.getLine(info);
      my_sound_effect.open(game_audio_stream);
    } catch (IOException e) {
      e.printStackTrace();
    } catch (LineUnavailableException e)
    {
      e.printStackTrace();
    }
    return (SoundEffect) my_sound_effect;
  }

  public /*@ pure @*/ boolean playing() {
    //assert false; //@ assert false;
    return my_sound_effect.isRunning();
  }

  /**
   * Start playing the music.
   */
  //@ ensures is_playing;
  public void start() {
    my_sound_effect.loop(1);
  }
}
