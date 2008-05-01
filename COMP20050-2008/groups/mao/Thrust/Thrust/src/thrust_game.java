import java.awt.Frame;
import java.awt.GraphicsEnvironment;
import java.awt.GraphicsDevice;
import java.awt.GraphicsConfiguration;
import java.awt.Dimension;
import java.awt.Toolkit;
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
			//draw frame
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
	GraphicsDevice tempThree = tempTwo[0];
	GraphicsConfiguration[] tempFour = tempThree.getConfigurations();
	
	myFrame = new Frame("Thrust game", tempFour[0]);
	myFrame.setVisible(true);
	myFrame.setSize(400,400);
	}

	
	private void drawFrame()
	{
	
	
	}
	
	
}