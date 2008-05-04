import java.io.BufferedReader;
import java.io.FileReader;


class thrustMap
{
	// Size of 
	char[][] myMap = new char[55][24];

	public thrustMap(String fileName)
	{
		try
        { 
		BufferedReader tempOne = new BufferedReader(new FileReader(fileName));
			while(tempOne.read() != -1)
			{
				
			
			}
		}
		catch(Exception e)
		{	
		}		
	}

}