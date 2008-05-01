import java.awt.event.KeyListener;
import java.awt.event.ActionListener;
java.awt.event.KeyEvent;
// thrust game thread

class thrust_game implements Runnable, KeyListener, ActionListener
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
			System.out.print(currentChar);
			}
			catch(Exception e)
			{
			System.out.println(e);
			}
		}
	}
	
	
	public void keyTyped(KeyEvent e) 
	{
    }
    
	public void keyPressed(KeyEvent e) 
	{
	currentChar = (int)e.getKeyChar();
	}
	
    
    public void keyReleased(KeyEvent e)
	{
    }
}