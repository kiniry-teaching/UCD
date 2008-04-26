package thrust.input;

/**
 * Processes and delegates each keyboard input received.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 April 2008
 */
public class InputHandler 
{
    private static boolean gameRunning = false;

    // Enumeration of Valid commands

    private enum validChar
    {
	DISPLAY_HIGH_SCORES(104, true),
	TOGGLE_MUSIC_OR_EFFECTS(109, false),
	START_GAME(32, true), 
	STOP_GAME(27, true),
	FIRE_GUN(13, false),
	TURN_LEFT(97, false), 
    TURN_RIGHT(115, false),
	USE_ENGINE(15, false),
	USE_SHIELD(32, false);

	private final int myAscii;
	private final char myChar;
	private final boolean stateAccess;

	private validChar(int i, boolean canChangeGameState)
        {
	myAscii = i;
	myChar = (char)i;
	stateAccess = canChangeGameState;
        }

	public int getAscii()
	{
        return myAscii;
	}

	public char getChar()
	{
        return myChar;
	}
	
	public boolean getStateAccess()
	{
        return stateAccess;
	}

    }

   

  /**
   * @return What are the legal keyboard inputs?
   */
    public /*@ pure @*/ char[] legal_inputs()
    {
       	int count = 0;
       	char[] tempOne;
       	for(validChar i : validChar.values())
       	    {
	       	count++;
       	    }
       	tempOne = new char[count];
       	count = 0;
       	for(validChar i : validChar.values())
	    {
		tempOne[count] = i.getChar();
			count++;
	    }
       	return tempOne;   
    }

  /**
   * @return Is this character a legal keyboard input?
   * @param the_character the character to check.
   */
  /*@ ensures \result <==> (the_character == DISPLAY_HIGH_SCORES) |
    @                      (the_character == TOGGLE_MUSIC_OR_EFFECTS) |
    @                      (the_character == START_GAME) |
    @                      (the_character == STOP_GAME) |
    @                      (the_character == FIRE_GUN) |
    @                      (the_character == TURN_LEFT) |
    @                      (the_character == TURN_RIGHT) |
    @                      (the_character == USE_ENGINE) |
    @                      (the_character == USE_SHIELD);
    @*/
    public /*@ pure @*/ boolean legal_input(char the_character)
    {
       	for(validChar i : validChar.values())
	    {
		if(i.getChar() == the_character)
		    {
			return true;
		    }
	    } 
	return false;
    }

  /**
   * Process this keyboard input character.
   * @param the_keyboard_input the input character to process.
   */
  //@ requires legal_input(the_keyboard_input);
    public void process(char the_keyboard_input)
    {
		for(validChar i : validChar.values())
		{
			if(i.getChar == the_keyboard_input)
			{
				if(i.getStateAccess() == true)
				{
					if(gameRunning == true)
					{
					gameRunning = false;
					}
					else
					{
					gameRunning = true;
					}
				}
			}
		}
	}
}
