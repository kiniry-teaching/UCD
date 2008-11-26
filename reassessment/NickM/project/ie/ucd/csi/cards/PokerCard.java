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
	  /**
	   * Returns the suite of this card.
	   */
	  public byte suite() {			
			return suite;
	  }
	  /**
	   * Returns the (numberical) value of this card.
	   */
	  public byte value() {
		  return value;
	  }
	  /**
	   * Checks if parameter s is a valid suite.
	   */
	  public boolean validSuite(byte s) {
		
		  if (-1 < s && s < 4) return true;
		  else return false;
	  }
	  /**
	   * Checks if parameter v is a valid value.
	   */
	  public boolean validValue(byte v) {
		
		  if (-14 < v && v < 0) return true;
		  else return false;
	  }

	  /**
	   * Returns true if this card has the same face value
	   * as the parameter Card.
	   */
	  public boolean sameFaceValueAs(Card a_card) {
		
		  return a_card.value() == value;
	  }
	  
	  /**
	   * Returns true if this card has the same suite 
	   * as the parameter Card.
	   */
	  public boolean sameSuiteAs(Card a_card) {
		
		  return a_card.suite() == suite;
	  }
	  
	  /**
	   * Returns true if this card has a greater face 
	   * (numerical) value as that of the parameter Card.
	   */
	  public boolean greaterFaceValueThan(Card a_card) {

		  if (a_card.value() < value) return true;
		  else return false;
	  }

	  /**
	   * This method is not needed in the game Poker, 
	   * as it has no wildcards or trumps, so I've just
	   * left it the same as greaterFaceValueThan()
	   */
	  public boolean greaterValueThan(Card a_card) {
		
		  if (a_card.value() < value) return true;
		  else return false;
	  }

	  public boolean equivalentTo(Card a_card) {
	
		  if ( (a_card.value() == value) && 
			   (a_card.suite() == suite)) return true;
		  else return false;
	  }

}