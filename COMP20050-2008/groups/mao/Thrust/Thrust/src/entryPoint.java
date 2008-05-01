// Entrypoint into the game

class entryPoint
{
	public static void main(String[] args)
	{
	// Creates a new thread, running at the thrust_game constructor's int as frames per second
	new Thread(new thrust_game(30)).start();
	}
}