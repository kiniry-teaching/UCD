package thrust.audio;
import sun.audio.*;    //import the sun.audio package
import java.io.*;

public class Music {
  //@ public model boolean is_playing;

  InputStream in = new FileInputStream(Thrust_music.mp3);
  AudioStream as = new AudioStream(in); 
  AudioData data = as.getData();
  ContinuousAudioDataStream cas = new ContinuousAudioDataStream(data);

  /**
   * @return Is music playing?
   */
  //@ ensures \result == is_playing;
  public /*@ pure @*/ boolean playing() {
    assert false; //@ assert false;
    return false;
  }

  /**
   * Start playing the music.
   */
  //@ ensures is_playing;
  public void start() {
    AudioPlayer.player.start(cas);
//    assert false; //@ assert false;
  }

  /**
   * Stop playing the music.
   */
  //@ ensures !is_playing;
  public void stop() {
    AudioPlayer.player.stop(cas);
//    assert false; //@ assert false;
  }
}
