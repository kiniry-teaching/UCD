package GUI;

import java.util.LinkedList;
import java.util.Vector;

/**
 * @author Alex Rankin
 *
 */
public class Cocktail {
	LinkedList<String> cocktail = new LinkedList<String>();
	String name;
	String about;
	boolean available;
	boolean stir, ice;
	double price = 0;
	
	/**
	 * Makes a new Coktail Object with the name n
	 * @param n Name of the cocktail
	 */
	public Cocktail(String n) {
		setName(n);
		available = false;
	}

	/**
	 * Returns the list of ingredients of the cocktail
	 * @return cocktail
	 */
	public LinkedList<String> getList(){
		return cocktail;
	}
	
	/**
	 * Calculates the price of a cocktail
	 * @param b Vector of beverage objects e.g the Cocktail ingredients
	 */
	public void calcPrice(Vector<Beverage> b){
		price = 0;
		for(int i=0; i<cocktail.size(); i++){
			for(int j=0; j<b.size(); j++){
				if(b.get(j).getName().equalsIgnoreCase(cocktail.get(i))){
					price += b.get(j).getPrice();
				}
			}
		}
	}
	
	/**
	 * Gets the array to be sent to the NXT brick
	 * @param b Vector of beverage objects eg the Cocktail ingrediants
	 * @return toRet an integer array of position codes
	 */
	public int[] getArray(Vector<Beverage> b){
		int[] toRet = new int[cocktail.size()+2];
		for(int i=0; i<cocktail.size(); i++){
			for(int j=0; j<b.size(); j++){
				if(b.get(j).getName().equalsIgnoreCase(cocktail.get(i))){
					toRet[i] = b.get(j).getId();
				}
			}
		}
		
		if(ice) {
			toRet[cocktail.size()] = 0;
		}
		else {
			// 99 means skip
			toRet[cocktail.size()] = 99;
		}
		if(stir) {
			toRet[cocktail.size()+1] = 1;
		}
		else {
			// 99 means skip
			toRet[cocktail.size()+1] = 99;
		}
		return toRet;
	}
	
	/**
	 * Sets whether a drink requires stirring
	 * @param b Cocktail which stir is being set
	 */
	public void setStir(boolean b){
		stir = b;
	}
	
	/**
	 * Returns whether a drink requires stirring 
	 * @return stir a boolean value
	 */
	public boolean getStir(){
		return stir;
	}
	
	/**
	 * Sets whether a drink requires ice
	 * @param b true if ice is required false if not
	 */
	public void setIce(boolean b){
		ice = b;
	}
	
	/**
	 * Returns whether a drink requires stirring 
	 * @return ice a boolean value
	 */
	public boolean getIce(){
		return ice;
	}
	
	/**
	 * Sets whether a drink is currently available
	 * @param b true if yes false if no
	 */
	public void setAvail(boolean b){
		available = b;
	}
	
	/**
	 * Returns if a drink is available
	 * @return available a boolean value
	 */
	public boolean getAvail(){
		return available;
	}
	
	/**
	 * Adds a drink to the Cocktail
	 * @param in the name of the drink to be added
	 */
	public void addDrink(String in) {
		cocktail.add(in);
	}

	/**
	 * Sets the name of the Cocktail
	 * @param in the string containing the name
	 */
	public void setName(String in) {
		name = in;
	}
	
	/**
	 * Returns the name of the Cocktail
	 * @return name a string containing the name of the Cocktail
	 */
	public String getName(){
		return name;
	}

	/**
	 * Sets the location of the description file of a Cocktail
	 * @param in string containing file location
	 */
	public void setDescription(String in) {
		about = in;
	}

	/**
	 * Returns the price of the Cocktail
	 * @return price a double containing the drinks total price
	 */
	public double getPrice() {
		return price;
	}
}
