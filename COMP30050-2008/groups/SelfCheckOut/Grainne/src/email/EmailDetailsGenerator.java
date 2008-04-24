package email;
import java.util.*;


public class EmailDetailsGenerator 
{
	
	//Customer currentCustomer;
	
	/*
	 * Requests the current customer object from the recipe/receipt generator.
	 */
	public Object getCustomerObject()
	{
		//Customer currentCustomer = RecipeReceiptGenerator.getCustomer();
		return currentCustomer;
	}
	
	 /**
     * The recipe/receipt generator will send a customer object to the email client
     * containing customer name and email address
     */
    public String getCustomerName()
    {
    	//currentCustomer.getName();
    	return null;
    }
    
    /**
     * The recipe/receipt generator will send a customer object to the email client
     * containing customer name and email address
     */
    public String getCustomerEmail()
    {
    	//currentCustomer.getEmail();
    	return null;
    }
    
    /**
     * Gets a recipe object
     * 
     **/
    public Object getRecipes(Recipe r)
    {
    	//r.name;
    	//r.otheringredients;
    	//r.recipe;
    	return null;
    }

    /**
     * Gets receipt from receipt/recipe manager
     * Has an interface with the receipt/recipe manager
     **/
    public Object getReceipts(LinkedList<String> l)
    {
    	for(int i =0; i<l.size();i++)
    	{
    		//messageBody.append(l[i]);
    	}
    	
    	return null;
    }

}
