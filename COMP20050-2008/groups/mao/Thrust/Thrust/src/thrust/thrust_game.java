import java.util.Scanner;
 import java.io.InputStreamReader;

// thrust game thread

class thrust_game implements Runnable
{
	private int framesPerSecond;
	
	public thrust_game(int fps)
	{
	framesPerSecond = fps;
	}

	public void run()
	{
	InputStreamReader tempOne = new InputStreamReader(System.in);
	char tempTwo;
		while(true)
		{
		// Frame calculation and interrupt
			try
			{
			Thread.sleep(1000/framesPerSecond);
			tempTwo = (char)tempOne.read();
			System.out.print(tempTwo);
			tempTwo = 0;	
			}
			catch(Exception e)
			{
			System.out.println(e);
			}
		}
	}
}