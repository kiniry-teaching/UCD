/**
 * @author  patrick Nevin: 06754155
 * @created 02/04/08 version 0.1
 */
public class Keyboard_input 
{   
	/**
	 * @requires (int)key_code >= 0 && (int)key_code <= 255
     * ensures true;
     */
	/**
	 * @ invariant Keycodes are set exactly once per keyboard input.
	 */
	private char key_code;
	
	/**
	 * @return  What is your keycode?
	 */	
	private char key_code()
	{
		return this.key_code;
	}
	/**
	 * check what's d crack wif dis as he said commands only return voids
	 * but this methods obviously requires a bool
	 * @param key
	 * @return This character is your keycode
	 */

	private boolean is_key_code(char key)
	{
		return (key == this.key_code());
	}
}


