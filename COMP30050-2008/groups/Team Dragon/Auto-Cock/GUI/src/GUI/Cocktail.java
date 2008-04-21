package GUI;

import java.util.LinkedList;
import java.util.Vector;

/**
 * @author Lister
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
	 * @param n
	 */
	public Cocktail(String n) {
		setName(n);
		available = false;
	}

	public LinkedList<String> getList(){
		return cocktail;
	}
	
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
	
	public int[] getArray(Vector<Beverage> b){
		int[] toRet = new int[cocktail.size()+2];
		for(int i=0; i<cocktail.size(); i++){
			for(int j=0; j<b.size(); j++){
				if(b.get(j).getName().equalsIgnoreCase(cocktail.get(i))){
					toRet[i] = b.get(j).getId();
				}
			}
		}
		
		if(stir){
			toRet[cocktail.size()] = 499;
		}
		else{
			toRet[cocktail.size()] = 498;
		}
		if(stir){
			toRet[cocktail.size()+1] = 999;
		}
		else{
			toRet[cocktail.size()+1] = 998;
		}
		return toRet;
	}
	
	public void setStir(boolean b){
		stir = b;
	}
	
	public boolean getStir(){
		return stir;
	}
	
	public void setIce(boolean b){
		ice = b;
	}
	
	public boolean getIce(){
		return ice;
	}
	
	public void setAvail(boolean b){
		available = b;
	}
	
	public boolean getAvail(){
		return available;
	}
	
	/**
	 * @param in
	 */
	public void addDrink(String in) {
		cocktail.add(in);
	}

	/**
	 * @param in
	 */
	public void setName(String in) {
		name = in;
	}
	
	public String getName(){
		return name;
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
	public double getPrice() {
		return price;
	}

	/**
	 * @return
	 */
//	public byte[] getId() {
//		Beverage temp;
//		byte[] order = new byte[cocktail.size()];
//		for (int i = 0; i < cocktail.size(); i++) {
//			temp = cocktail.get(i);
//			order[i] = (byte) temp.getId();
//		}
//		return order;
//	}
}
