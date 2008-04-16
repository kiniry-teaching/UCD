package thrust.audio;

import java.io.FileInputStream;

import javax.sound.sampled.AudioFormat;
import javax.sound.sampled.AudioInputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.DataLine;
import javax.sound.sampled.SourceDataLine;
   


/**
 * In-game music.
 * @author Ciaran Flynn: 06516564
 *         Patrick Nevin: 06754155  
 *         Robert Plunkett: 06038883
 * @version 7 April 2008
 */


  public class Music {
  

    private boolean isPlaying = false;

    FileInputStream music = new FileInputStream("../media/Thrust_music.wav");

    AudioInputStream audioInputStream = music;

    AudioFormat aF = music.getFormat();
    DataLine.Info info = new DataLine.Info ( SourceDataLine.class, aF );


    int frameRate = (int)music.getFrameRate();
    int frameSize = music.getFrameSize();
    int bufSize = frameRate * frameSize / 10;




 
  
  public boolean playing() {

        return isPlaying;
  }

  
  public void start() {

	  SourceDataLine line = (SourceDataLine)AudioSystem.getLine( info );

	  line.open( music, bufSize );
       
	  line.start();

}
    


  public void stop() {
      
	  line.drain();
	  line.stop();
	  line.close();
 }

}

