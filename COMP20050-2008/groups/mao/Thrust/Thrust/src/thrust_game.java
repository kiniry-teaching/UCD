import thrust.input.*;
// thrust game thread

class thrust_game extends InputHandler implements Runnable 
{
	private int myFramesPerSecond;
	private int myCurrentChar;
	//private InputHandler myInputHandler;
	
	public thrust_game(int fps)
	{
	myFramesPerSecond = fps;
	}

	public void run()
	{
	// test code
	
	int frame = 0;
	// end test code
	
		while(true)
		{
		
			try
			{
			// Frame calculation and interrupt		
			Thread.sleep(1000/myFramesPerSecond);
			System.out.println(frame++);
			}
			catch(Exception e)
			{
			System.out.println(e);
			}
		}
	}
}