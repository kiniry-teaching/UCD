package GUI;
import java.util.LinkedList;

/**
 * @author Lister
 *
 */
public class Cocktail {
	LinkedList<Beverage> cocktail = new LinkedList<Beverage>();
	String name;
	String about;
	int price = 0;

	/**
	 * @param n
	 */
	public Cocktail(String n) {
		setName(n);
	}

	/**
	 * @param in
	 */
	public void addDrink(Beverage in) {
		cocktail.add(in);
	}

	/**
	 * @return
	 */
	public boolean ingredsAvail() {
		for (int i = 0; i < cocktail.size(); i++) {
			if (!cocktail.get(i).getAvailable()) {
				return false;
			}
		}
		return true;
	}

	/**
	 * @param in
	 */
	public void setName(String in) {
		name = in;
	}

	/**
	 * 
	 */
	public void setPrice() {
		Beverage temp;
		for (int i = 0; i < cocktail.size(); i++) {
			temp = cocktail.get(i);
			price += temp.getPrice();
		}
	}

	/**
	 * @param in
	 */
	public void setDescription(String in) {
		about = in;
	}

	/**
	 * @return
	 */
	public int getPrice() {
		return price;
	}

	/**
	 * @return
	 */
	public byte[] getId() {
		Beverage temp;
		byte[] order = new byte[cocktail.size()];
		for (int i = 0; i < cocktail.size(); i++) {
			temp = cocktail.get(i);
			order[i] = (byte) temp.getId();
		}
		return order;
	}
}
