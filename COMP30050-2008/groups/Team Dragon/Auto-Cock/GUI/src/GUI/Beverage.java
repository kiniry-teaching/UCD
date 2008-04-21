package GUI;

/**
 * @author Lister
 *
 */
public class Beverage {
	int price;
	boolean alcoholic;
	private boolean available;
	String name;
	int id;

	/**
	 * @param n
	 * @param p
	 * @param a
	 * @param i
	 */
	public Beverage(String n, int p, boolean a, int i) {
		name = n;
		price = p;
		alcoholic = a;
		id = i;
		available = false;
	}

	/**
	 * @return
	 */
	public int getPrice() {
		return price;
	}

	/**
	 * 
	 */
	public void setAvailable(boolean b) {
		available = b;
	}

	/**
	 * @return
	 */
	public boolean getAvailable() {
		return available;
	}

	/**
	 * @return
	 */
	public boolean getAlcoholic() {
		return alcoholic;
	}

	/**
	 * @return
	 */
	public String getName() {
		return name;
	}

	/**
	 * @return
	 */
	public int getId() {
		return id;
	}

	/**
	 * @param in
	 */
	public void setPrice(int in) {
		price = in;
	}

	/**
	 * @param in
	 */
	public void setAlcoholic(int in) {
		if (in == 1)
			alcoholic = true;
		else
			alcoholic = false;
	}

	/**
	 * @param in
	 */
	public void setName(String in) {
		name = in;
	}

	/**
	 * @param in
	 */
	public void setId(int in) {
		id = in;
	}

}
