package thrust.maps;

public class mapSection
{
	public String mySectionHeader;
	public String mySectionDetails;
	public String[] mySectionLines;
	
	public mapSection(String head, String details)
	{
	// Store details of map section from map file
	mySectionHeader = head.trim();
	mySectionDetails = details.trim();;
	mySectionLines = mySectionDetails.trim().split("\n");
	}
}