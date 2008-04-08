import java.util.LinkedList;


public class Cocktail {
	LinkedList<Beverage> cocktail = new LinkedList<Beverage>();
	String name;
	String about;
	int price = 0;
	
	public Cocktail(String n) {
		setName(n);
	}
	
	public void addDrink(Beverage in)
	{
		cocktail.add(in);
	}
	
	public boolean ingredsAvail() {
		for(int i = 0; i<cocktail.size(); i++) {
			if(!cocktail.get(i).getAvailable()) {
				return false;
			}
		}
		return true;
	}
	
	public void setName(String in)
	{
		name = in;
	}
	
	public void setPrice()
	{	
		Beverage temp;
		for(int i = 0; i < cocktail.size(); i++)
		{
			temp = cocktail.get(i);
			price += temp.getPrice();
		}
	}
	
	public void setDescription(String in)
	{
		about = in;
	}
	
	public int getPrice()
	{
		return price;
	}
	
	public byte[] getId()
	{
		Beverage temp;
		byte[] order = new byte[cocktail.size()];
		for(int i = 0; i < cocktail.size(); i++)
		{
			temp = cocktail.get(i);
			order[i] = (byte)temp.getId();
		}
		return order;
	}
}
