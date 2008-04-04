
package thrust.audio;

public class Music {


  /**
   * @return Is music playing?
   */

    private boolean isPlaying = false;
  
  public boolean playing() {
   
    return isPlaying;
  }

  /**
   * Start playing the music.
   */

  public void start() {
      isPlaying = true;


  }

  /**
   * Stop playing the music.
   */
  
  public void stop() {
      isPlaying = false;
  }
}