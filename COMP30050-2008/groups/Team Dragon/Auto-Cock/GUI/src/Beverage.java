
public class Beverage {
	int price;
	boolean alcoholic;
	private boolean available;
	String name;
	int id;
	
	public Beverage(String n, int p, boolean a, int i)
	{
		name = n;
		price = p;
		alcoholic = a;
		id = i;
		available = false;
	}
	
	public int getPrice()
	{
		return price;
	}
	
	public void setAvailable(){
		available = !available;
	}
	
	public boolean getAvailable() {
		return available;
	}
	
	public boolean getAlcoholic()
	{
			return alcoholic;
	}
	
	public String getName()
	{
		return name;
	}
	
	public int getId()
	{
		return id;
	}
	public void setPrice(int in)
	{
		price = in;
	}
	
	public void setAlcoholic(int in)
	{
		if(in == 1)
			alcoholic = true;
		else
			alcoholic = false;
	}
	
	public void setName(String in)
	{
		name = in;
	}
	
	public void setId(int in)
	{
		id = in;
	}
	
}
