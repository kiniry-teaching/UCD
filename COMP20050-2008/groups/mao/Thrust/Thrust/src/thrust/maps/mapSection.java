package thrust.maps;

public class mapSection
{
	public String mySectionHeader;
	public String mySectionDetails;
	public String[] mySectionLines;
	
	public mapSection(String head, String details)
	{
	mySectionHeader = head.trim();
	mySectionDetails = details.trim();;
	mySectionLines = mySectionDetails.trim().split("\n");

	}
}