/*
 * UCD CSI Playing Card System.
 * $Id: PokerCard.java 1096 2005-08-24 23:02:36Z jkiniry $
 */

package ie.ucd.csi.cards;

/**
 * A standard playing card.
 *
 * @author Joseph Kiniry <joseph.kiniry@ucd.ie>
 */

public class PokerCard implements Card {

	  private byte suite, value;	
		
	  public PokerCard(byte suite, byte value) {
		  
		  this.suite = suite;
		  this.value = value;
	  }

	  public String toString() {
	    String cardString = Byte.toString(value)+" of "+Byte.toString(suite)+"s.";
	    return cardString;
	  }
	  
	  // Is this method not deprecated by the sameValue/SuiteAs 
	  // and equivelantTo methods?
	  public boolean equals(Card o) {
		  
		  return false;
	  }
	  
	  public byte suite() {
			
			return suite;
	  }

	  public byte value() {
		
		  return value;
	  }
	  public boolean validSuite(byte s) {
		
		  if (-1 < s && s < 5) return true;
		  else return false;
	  }


	  public boolean validValue(byte v) {
		
		  if (-15 < v && v < 0) return true;
		  else return false;
	  }

	  public boolean sameFaceValueAs(Card a_card) {
		
		  return value.equals(a_card.value);
	  }
	  

	  public boolean sameSuiteAs(Card a_card) {
		
		  return suite.equals(a_card.suite);
	  }
	
	  public boolean greaterFaceValueThan(Card a_card) {

		  if (value.compareTo(a_card.value) > 0) return true;
		  else return false;
	  }


	  public boolean greaterValueThan(Card a_card) {
		
		  if (value.compareTo(a_card.value) > 0) return true;
		  else return false;
	  }

	  public boolean equivalentTo(Card a_card) {
	
		  if ( (value.equals(a_card.value)) && 
				  (suite.equals(a_card.suite)) ) return true;
		  else return false;
	  }

}