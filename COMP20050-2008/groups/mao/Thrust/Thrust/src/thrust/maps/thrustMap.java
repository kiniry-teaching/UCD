package thrust.maps;

import java.io.BufferedReader;
import java.io.FileReader;



public class thrustMap
{
	// Size of 
	private char[][] myMap = new char[55][24];
	private String[] myMapLines = new String[24];


	public thrustMap(String fileName)
	{
		try
        { 
		BufferedReader tempOne = new BufferedReader(new FileReader(fileName));
		int tempTwo = 0;
			while(tempOne.ready())
			{
			myMapLines[tempTwo] = tempOne.readLine();
			tempTwo++;
			}
			
		System.out.println(myMapLines);
		}
		catch(Exception e)
		{	
		}		
	}
	
	public String getRawMap()
	{
	String tempOne = "";
		for(String a : myMapLines)
		{
		tempOne = tempOne + a;
		}
	return tempOne;
	}
	
	private void filterMapFile()
	{
	
	
	}
	

}