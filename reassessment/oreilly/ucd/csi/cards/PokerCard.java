/*
 * UCD CSI Playing Card System.
 * $Id: PokerCard.java 1096 2005-08-24 23:02:36Z jkiniry $
 */

package ie.ucd.csi.cards;

import ie.ucd.csi.cards;

/**
 * A standard playing card.
 * 
 * @author Joseph Kiniry <joseph.kiniry@ucd.ie>
 */

public class PokerCard implements Card {

	public byte suit;
	public byte value;

	public PokerCard(byte suit, byte value) {
	  PokerCard poker = new PokerCard(byte suit, byte value);
  }

	public String toString() {
        return "Suit: " + suit + ", Value: " + value;
	}

	/*
	 * @bug Card o should in fact be Object o e.g.PokerDeck.
	 * 
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	public boolean equals(Object o) {
		if (o instanceof Card) {
			return value.equals(o.value());
		} else {
			return false;
		}
	}

	/** The suite of this card. */
	public byte suit() {
		return suit;
	}

	/**
	 * Is 's' a valid suite?
	 * 
	 * @param s
	 *            a value to check to see if it is a valid suite.
	 * @return true iff 's' is a valid suite.
	 */
	public boolean validSuit(byte s) {
		return s == CLUB || s == DIAMOND || s == HEART || s == SPADE;
	}

	/** The face-value of this card */
	public byte value() {
		return value;
	}

	/**
	 * Is 'v' a valid face-value?
	 * 
	 * @param v
	 *            the value to check to see if it is a valid face-value.
	 * @return true iff 'v' is a valid face-value.
	 */
	public boolean validValue(byte v) {
		return v == ACE || v == TWO || v == THREE || v == FOUR || v == FIVE
				|| v == SIX || v == SEVEN || v == EIGHT || v == NINE
				|| v == TEN || v == JACK || v == QUEEN || v == KING;
	}

	/**
	 * @param a_card
	 *            the card to compare
	 * @return true iff the suite of this card is identical to the suite of
	 *         <code>a_card</code>
	 */
	public boolean sameSuitAs(Card a_card) {
		return suit == a_card.suit();
	}

	/**
	 * @param a_card
	 *            the card to compare
	 * @return true iff the face value of this card is identical to the face
	 *         value of <code>a_card</code>
	 */
	public boolean sameFaceValueAs(Card a_card) {
		return value == a_card.value();
	}

	/**
	 * @param a_card
	 *            the card to compare
	 * @return true iff the face value of this card is strictly greater than the
	 *         face value of <code>a_card</code>
	 */
	public boolean greaterFaceValueThan(Card a_card) {
		return value > a_card.value();
	}

	/**
	 * Whether this card has a greater value than <code>a_card</code> is
	 * determined by a given card game's rules.
	 * 
	 * @param a_card
	 *            the card to compare
	 * @return true iff this card has a great value than <code>a_card</code>
	 */
	public boolean greaterValueThan(Card a_card) {
		return value > a_card.value();

	}

	/**
	 * Two cards are equivalent if they are indistinguishable in a given card
	 * game's rules.
	 * 
	 * @param a_card
	 *            the card to compare
	 * @return true iff this card and <code>a_card</code> are indistinguishable
	 */
	public boolean equivalentTo(Card a_card) {
		return value == a_card.value() && suit == a_card.suit();
	}
	
    public int hashCode(){
        int hash = suit;
        hash <<= 8;
        hash |= value;
        
        return hash;
    }

    public int compareTo(Card a_card){
        if (this.sameFaceValueAs(a_card))
            return 0;
        else if (this.greaterFaceValueThan(a_card))
            return 1;
        return -1;
    }
}
