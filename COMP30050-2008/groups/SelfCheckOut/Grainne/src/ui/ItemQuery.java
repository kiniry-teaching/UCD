package ui;

//ItemQuery.java class designed to create a new product object,
//create query based on a barcode, return all necessary data,
//eliminates need for two seperate classes, replaces Product.java and
//Query.java

import java.sql.*;
 // BarCode barcode;
 

public class ItemQuery
{

	  String name;
	  double price;
	  int minweight;
	  int weight;
	  int maxweight;
	  String soundfile;
	  String imagefile;
	  String allergy;
	  int primeitem;
 
	  public ItemQuery(double bc)
	  {
		  name = "pajo";
		  price = 99;
		  allergy = "pajo likes cats";
	  }
}
