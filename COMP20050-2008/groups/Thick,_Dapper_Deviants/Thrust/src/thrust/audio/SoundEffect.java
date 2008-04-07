package thrust.audio;

import java.io.File;
import java.io.*;
import javax.sound.sampled.*;

/**
 * Any sound made in response to a event.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class SoundEffect {
  private AudioFormat format;
  private byte[] samples;
  /**
   * This is your sound effect.
   * @param the_sound_effect_file the sound effect to make.
   * @return the new sound effect for the effect stored in 's'.
   */
  public byte[] getSamples(){
    return samples;
  }
  private byte[] getSamples(AudioInputStream audioStream){
    int length = (int)(audioStream.getFrameLength()*format.getFrameSize());
    byte[] samples = new byte[length];
    DataInputStream is = new DataInputStream(audioStream);
    try{
      is.readFully(samples);
    }catch (Exception ex){
      ex.printStackTrace();
    }
    return samples;
  }
  
  public SoundEffect(String the_sound_effect_file) {
    try{
      AudioInputStream stream = AudioSystem.getAudioInputStream(new File(the_sound_effect_file));
      format = stream.getFormat();
      samples = getSamples(stream);
    }catch (Exception ex){
      ex.printStackTrace();
      }
  }
  public void start(InputStream source){
    int bufferSize = format.getFrameSize()*Math.round(format.getSampleRate()/10);
    byte[] buffer = new byte[bufferSize];
    SourceDataLine line;
    try{
      DataLine.Info info = new DataLine.Info(SourceDataLine.class,format);
      line = (SourceDataLine)AudioSystem.getLine(info);
      line.open(format,bufferSize);
    }catch(Exception ex){
      ex.printStackTrace();
      return;
    }
    line.start();
    try{
      int numBytesRead = 0;
      while(numBytesRead != -1){
        numBytesRead = source.read(buffer,0,buffer.length);
        if(numBytesRead != -1){
          line.write(buffer,0,numBytesRead);
        }
      }
    }catch(Exception ex){
      ex.printStackTrace();
    }
    line.drain();
    line.close();
  }
  /**
   * Start playing your effect.
   */
  public static void main(String[] args){
    SoundEffect sound = new SoundEffect("/Users/davidmurphy/Desktop/2");
    InputStream stream = new ByteArrayInputStream(sound.getSamples());
    sound.start(stream);
    System.exit(0);
  }
}
