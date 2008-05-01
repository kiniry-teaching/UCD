import java.awt.event.KeyListener;
import java.awt.event.KeyEvent;
// thrust game thread

class thrust_game implements Runnable, KeyListener
{
	private int framesPerSecond;
	private int currentChar;
	
	public thrust_game(int fps)
	{
	framesPerSecond = fps;
	}

	public void run()
	{
		while(true)
		{
		// Frame calculation and interrupt		
			try
			{
			Thread.sleep(1000/framesPerSecond);
			}
			catch(Exception e)
			{
			System.out.println(e);
			}
		}
	}
	
	// <Overwrite methods>
	public void keyTyped(KeyEvent e) 
	{
    }
    
	public void keyPressed(KeyEvent e) 
	{
	currentChar = (int)e.getKeyChar();
	System.out.println(currentChar);
	}
	 
    public void keyReleased(KeyEvent e)
	{
    }
	
	// </Overwrite methods>
}