package email;
import java.awt.*;
import javax.swing.*;
import database.getCustomer;
import database.getRecipe;
import database.getTransaction;
import java.util.LinkedList;
import database.Item;


/**
 * @author Grainne Mulligan
 * */

public class EmailDetailsGenerator 
{

	
	/*
	 * Requests the current customer object from the recipe/receipt generator.
	 */
	public Customer getCustomerObject(int customerNr)
	{
		Customer currentCustomer = RecipeReceiptGenerator.getCustomer();
		return currentCustomer;
	}

    
    /**
     * Gets a recipe object
     * 
     **/
    public Recipe getRecipes(Recipe r)
    {
    	r=currentRecipe;
    	return currentRecipe;
    }

    /**
     * Gets receipt from receipt/recipe manager
     * Has an interface with the receipt/recipe manager
     **/
    public LinkedList<String> getReceipts(LinkedList<String> l)
    {
    	l=currentTransaction;
    	return currentTransaction;
    }

}
