import java.awt.DisplayMode;
import java.awt.Frame;
import java.awt.GraphicsDevice;
import java.awt.GraphicsConfiguration;
import java.awt.GraphicsEnvironment;
import java.awt.Rectangle;

import thrust.input.InputHandler;
// thrust game thread

class thrust_game extends InputHandler implements Runnable 
{
	private int myFramesPerSecond;
	private int myCurrentChar;
	private Frame myFrame;
	//private InputHandler myInputHandler;
	
	public thrust_game(int fps)
	{
	myFramesPerSecond = fps;
	}

	public void run()
	{
	initFrame();
		while(true)
		{
		
			try
			{
			// Frame calculation and interrupt		
			Thread.sleep(1000/myFramesPerSecond);
			drawFrame();
			}
			catch(Exception e)
			{
			System.out.println(e);
			}
		}
	}
	
	
	private void initFrame()
	{
	
	

	GraphicsEnvironment tempOne = GraphicsEnvironment.getLocalGraphicsEnvironment();
    GraphicsDevice[] tempTwo = tempOne.getScreenDevices();
	int tempThree = tempTwo[0].getDisplayMode().getWidth(); // Current screen width
	int tempFour = tempTwo[0].getDisplayMode().getHeight(); // Current screen height
	
	//myFrame = new Frame(
	
	}
	
	private void drawFrame()
	{
	
	
	}
	
	
}