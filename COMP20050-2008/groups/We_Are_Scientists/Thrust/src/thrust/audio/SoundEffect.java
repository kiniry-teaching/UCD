package thrust.audio;

import java.io.File;

import javax.sound.sampled.*;

/**
 * Any sound made in response to a event.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class SoundEffect {
  /**
   * This is your sound effect.
   * @param the_sound_effect_file the sound effect to make.
   * @return the new sound effect for the effect stored in 's'.
   */
  //public static void main(String[] args) throws Exception {
  private  Clip clip;
  /**
   * Any sound made in response to a event.
   * @author simon
   * @param  soundFile sound file
   */
  public final/* @ pure @ */SoundEffect make(final File soundFile) {

    AudioInputStream sound = null;

      try {
            sound = AudioSystem.getAudioInputStream(soundFile);
          } catch (Exception e) {
            System.out.println("error");
          }
          //final AudioFormat format = audioInputStream.getFormat();
          final DataLine.Info info =
            new DataLine.Info(Clip.class, sound.getFormat());
          try {
            clip = (Clip) AudioSystem.getLine(info);
            clip.open(sound);
         } catch (Exception e) {
            System.out.println("error");
          }
          return null;
          // @ assert false;
        }

  /**
   * Start playing your effect.
   */
  public final void start() {
  clip.start();
  }
}
