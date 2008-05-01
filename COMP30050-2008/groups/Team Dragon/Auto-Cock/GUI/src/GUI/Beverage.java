package GUI;

/**
 * @author Alex Rankin
 * 
 */
public class Beverage {
	private int price;
	private boolean alcoholic;
	private boolean available;
	private String name;
	private int id;

	/**
	 * Constructs a new beverage object, and initialises required variables.
	 * 
	 * @param n The name of the beverage
	 * @param p The price of the beverage
	 * @param a Whether the beverage is alcoholic
	 * @param i The ID (position) of the beverage
	 */
	public Beverage(String n, int p, boolean a, int i) {
		name = n;
		price = p;
		alcoholic = a;
		id = i;
		available = false;
	}

	/**
	 * Gets the price of the beverage
	 * 
	 * @return The price of the beverage
	 */
	public int getPrice() {
		return price;
	}

	/**
	 * Sets whether the beverage is available
	 * 
	 * @param b Boolean telling us if the beverage is available
	 */
	public void setAvailable(boolean b) {
		available = b;
	}

	/**
	 * Checks whether the beverage is available
	 * 
	 * @return Boolean stating whether the beverage is available
	 */
	public boolean getAvailable() {
		return available;
	}

	/**
	 * Checks whether the beverage is alcoholic
	 * 
	 * @return Boolean stating whether the beverage is alcoholic
	 */
	public boolean getAlcoholic() {
		return alcoholic;
	}

	/**
	 * Get the name of the beverage
	 * 
	 * @return String containing the name of the beverage
	 */
	public String getName() {
		return name;
	}

	/**
	 * Get the ID (position) of the beverage
	 * 
	 * @return Integer containing the ID of the beverage
	 */
	public int getId() {
		return id;
	}

	/**
	 * Set the price of the beverage
	 * 
	 * @param in Integer representation of the price of this beverage
	 */
	public void setPrice(int in) {
		price = in;
	}

	/**
	 * Set whether the beverage is alcoholic
	 * 
	 * @param in Integer representing true if 1
	 */
	public void setAlcoholic(int in) {
		if (in == 1)
			alcoholic = true;
		else
			alcoholic = false;
	}

	/**
	 * Sets the name of the beverage
	 * 
	 * @param in The new name of this beverage
	 */
	public void setName(String in) {
		name = in;
	}

	/**
	 * Sets the ID of the beverage
	 * 
	 * @param in New ID of the beverage
	 */
	public void setId(int in) {
		id = in;
	}

}
