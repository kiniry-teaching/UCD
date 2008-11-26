/*
 * UCD CSI Playing Card System.
 * $Id: PokerHand.java 1100 2005-08-24 23:04:23Z jkiniry $
 */

package ie.ucd.csi.cards;

/**
 * A five card hand for poker.
 *
 * @author Joseph Kiniry <joseph.kiniry@ucd.ie>
 * @see http://secure.ucd.ie/~kiniry/part4.txt
 */

public class PokerHand {
	// Gave each type of hand a value based on their importance.
	public static final byte ROYAL_FLUSH = 10, STRAIGHT_FLUSH = 9, 
    	FOUR_OF_A_KIND = 8, FULL_HOUSE = 7, FLUSH = 6, STRAIGHT = 5, THREE_OF_A_KIND = 4,
    	TWO_PAIRS = 3, ONE_PAIR = 2, HIGH_CARD = 1, NOTHING = 0;

	  /** The thirteen standard card values. */
	  public static final byte TWO = 2, THREE = 3, FOUR = 4,
	    FIVE = 5, SIX = 6, SEVEN = 7, EIGHT = 8, NINE = 9, TEN = 10,
	    JACK = 11, QUEEN = 12, KING = 13, ACE = 14;
	
	private static PokerCard[] hand;
	public static byte count = 0;
	public static byte handValue;
  
	/**
	 * Creates new PokerHand, an array of PokerCards
	 * Array is set to size 5, but no elements are added until addCard method is used. 
	 */
	public PokerHand() {
		  
		hand = new PokerCard [5];
		count = 0;
		handValue = NOTHING;
	}

	/**
	 * Adds a PokerCard to the PokerHand, unless the PokerHand is already full.
	 * @param c
	 */
	public void addCard(PokerCard c) {
		
		if (count() == 5) System.out.println("Hand is full.");
		else {
			hand[count] = c;
			count++;
		}
	}
	/**
	 * Removes the parameter PokerCard, creates new PokerCard array with
	 * all elements except for parameter.
	 * @param c
	 */
	public void removeCard(PokerCard c) {
	  	  
		for (int x = 0 ; x < hand.length ; x++) {
		  
			if (c.equals(hand[x])) {
			  
				hand = new PokerCard[5];
				// add all PokerCards except for x into new array;
				count--;
			}
		}
	  	  
	}
	/**
	 * Returns the current amount of cards in the hand.
	 * */
	public byte count() {
		return count;
	}
  
	/**
	 * Added getter method for the value of this hand
	 * @return handValue
	 */
	public byte handValue() {
  		return handValue;
	}
  
  
  /**
   * Is this hand of higher value than the hand 'h'.
   *
   * Recall that in the rules of poker, the order of hand values is as
   * follows, highest to lowest:
   * 
   * ROYAL FLUSH  the five highest cards, namely
   * ace-king-queen-jack-ten of any one of the four suites.  The
   * suites have equal rank.  Royal flushes are of equal value.
   *
   * STRAIGHT FLUSH any five cards of the same suite in
   * numerical sequence, such as the ten-nine-eight-seven-six of
   * spades.  This flush is called "ten high".  Two flushes are
   * compared by comparing their top cards, e.g., a "ten high" beats a
   * "nine high".  If the top cards are the same, the hands are of
   * equal value.
   *
   * FOUR OF A KIND any four cards of the same
   * demonination.
   *
   * FULL HOUSE three of one kind and two of another.  In
   * evaluating two full houses, the hand with the highest three of a
   * kind wins.
   *
   * FLUSH any five cards of the same suite, but not in
   * sequence.  In evaluating two flushes, the winner is determined by
   * the rank of the highest card in the hand.  If the highest card is
   * the same, the next highest cards are compared, etc.  If all ranks
   * are equal, the hands are of equal value.
   *
   * STRAIGHT five cards in consecutive sequence but not of
   * the same suite.  In competing straights, the winner is decided by
   * the rank of the highest card.  Straights of the same denomination
   * are equal and tie.
   *
   * THREE OF A KIND three cards of the same numerical
   * value plus two different and irrelevant cards.  The hand having
   * the highest three of a kind wins, regardless of the value of the
   * unmatched cards.
   *
   * TWO PAIR two different pairs of cards plus one odd
   * card.  In evaluating two two-pair hands, the winner is the hand
   * with the highest pair.  If the highest pairs are tied, the rank
   * of the second pair in the hands determines the winner.  If the
   * second pair is also tied, the higher card of the odd cards
   * determines the winner.  If all cards of the competing hands are
   * of matching value, the hands are tied.
   *
   * ONE PAIR two cards of the same denomination plus three
   * indifferent unmatched cards.  The hand with the higher pair wins.
   * If the pairs have the same value, the highest indifferent card
   * wins, etc.  If all cards match, the hands tie.
   *
   * <li> high card </li> a hand which contains five indifferent cards
   * not of the same suite, not in sequence, and falling into none of
   * the above combinations.  Between two high card hands, the highest
   * card determines the winner, etc.  If all cards match, the hands
   * tie.
   *
   * </ol>
   *
   * If two hands are of the same type, then the hand with the highest 
   * rank wins.
   */

	/**
	 * Gets the value of this hand.
	    ROYAL_FLUSH = 10
		STRAIGHT_FLUSH = 9, 
    	FOUR_OF_A_KIND = 8
    	FULL_HOUSE = 7
    	FLUSH = 6
    	STRAIGHT = 5
    	THREE_OF_A_KIND = 4
    	TWO_PAIRS = 3
    	ONE_PAIR = 2
    	HIGH_CARD = 1
	 */
	public byte getHandValue(){
		
		// puts this pokerhand in ascending order
		orderHand();

		// finish handValue methods in morning...
		if (isRoyalFlush()) return ROYAL_FLUSH;
		else if (isStraightFlush()) return STRAIGHT_FLUSH;
		else if (isFourOfAKind()) return FOUR_OF_A_KIND;
		else if (isFullHouse()) return FULL_HOUSE;
		else if (isFlush()) return FLUSH;
		else if (isStraight()) return STRAIGHT;
		else if (isThreeOfAKind()) return THREE_OF_A_KIND;
		else if (isTwoPair()) return TWO_PAIRS;
		else if (isOnePair()) return ONE_PAIR;
		else return HIGH_CARD;
	}
	
	/** Tests if hand is a royal flush..
	 *	If its a flush and its a straight and the hand values are ten, jack
	 *	queen, king, ace -> it is a royal flush. 
	 *	
	 *@change isFlush() && isStraight() -> isStraightFlush 
	 */
	public static boolean isRoyalFlush() {
		
		if (isStraightFlush() && hand[0].value() == 10 && hand[1].value() == JACK && 
				 hand[2].value() == QUEEN && hand[3].value() == KING &&
				 hand[4].value() == ACE) return true;
		
		return false;
	}
	/** Tests if hand is a straight flush
	 * Just tests if isStraight and isFlush..
	 */
	public static boolean isStraightFlush() {
		
		if (isFlush() && isStraight()) return true;
		
		return false;
	}
	/** Tests if hand is four of a kind. 
	 * @bug: if count == 4 is outside the first for loop then it will add
	 * 		up the count of each card of the four of a kind so you end up
	 * 		with count == 16. Moved the count == 4 within the y loop and 
	 * 		set the count to 0 after each iteration of y loop.
	 * 
	 * */
	public static boolean isFourOfAKind() {
		
		int count = 0;
		
		for (int x = 0 ; x < hand.length ; x++) {
			for (int y = x+1 ; y < hand.length ; y++) {
				if (hand[x].value() == hand[y].value()) count++;
				if (count == 4) return true;
			}
			count = 0;
		}
	
		return false;
	}
	/** Tests if hand is a full house.
	 * 
	 * Cannot be fourofakind or two pair, as this leaves one card without a handvalue
	 * Basically can only be a three of a kind with a two of a kind.
	 * @note if this method is being called then it has already failed the 
	 * 			isFourOfAKind method (because they are called in descending order
	 * 			in the getHandValue method) but i'll leave in the check anyway.
	 */
	public static boolean isFullHouse() {

		// obviously then there would be 1 card not in a valued position.
		if (isFourOfAKind() || isTwoPair()) return false;
		
		// if it's one pair and also three of a kind and is NOT two pair or a full house
		// then it must be a full house.
		if (isOnePair() && isThreeOfAKind()) return true;
			
		return false;
	}
	
	/** Tests if hand is a flush. */
	public static boolean isFlush() {
		
		for (int x = 0 ; x < hand.length ; x++) {
			if ( !(hand[x].sameSuiteAs(hand[x+1])) ) {
				return false;
			}
		}
		return true;
	}
	
	/** Tests if hand is a straight. */
	public static boolean isStraight() {
		
		for (int x = 0 ; x < hand.length ; x++) {
			if (hand[x].value() != hand[x+1].value() - 1) {
				return false;
			}
		}
		return true;
	}
	/** Tests if hand is three of a kind.
	 * Same method as isFourOfAKind, only the count == 3.
	 */
	public static boolean isThreeOfAKind() {
		
		int count = 0;
		
		for (int x = 0 ; x < hand.length ; x++) {
			for (int y = x+1 ; y < hand.length ; y++) {
				if (hand[x].value() == hand[y].value()) count++;
				if (count == 3) return true;
			}
			count = 0;
		}
	
		return false;
	}
	/** Tests if hand is two pair.
	 * 
	 *  
	 */
	public static boolean isTwoPair() {
		
		int count = 0;
		int amountOfPairs = 0;
		
		for (int x = 0 ; x < hand.length ; x++) {
			
			for (int y = x+1 ; y < hand.length ; y++) {
				if (hand[x].value() == hand[y].value()) count++;
			}
			if (count == 2) amountOfPairs++;
			count = 0;
		}
		
		if (amountOfPairs == 2) return true;
		
		return false;
	}

	public static boolean isOnePair() {
		
		int count = 0;
		
		for (int x = 0 ; x < hand.length ; x++) {
			for (int y = x+1 ; y < hand.length ; y++) {
				if (hand[x].value() == hand[y].value()) count++;
				if (count == 2) return true;
			}
			count = 0;
		}
	
		return false;
	}
	/**
	 * Orders the PokerHand in ascending order.
	 */
	public static void orderHand() {
		
		for (int x = 0; x < hand.length; x++) {
			
	        PokerCard temp = hand[x]; 
	        int y = x;
	        
	        while(y > 0 && hand[y-1].value() >= temp.value()) { 
	            hand[y] = hand[y-1];
	            y--;
	        }
	        hand[y] = temp;
	    }
	}
	
	/**
	 * Compares this pokerhand's value to the parameter hand's value.
	 * @param h
	 * @return
	 */
	public boolean compare(PokerHand h) {
	  
		return getHandValue() == h.getHandValue();
	}

	/**
	 * Returns true if this pokerhand has a higher value then parameter hand.
	 * @note Switched method name from equal to higherValueThan to avoid confusing method names
	 * @see #higherValueThan(PokerHand)
	 */
	public boolean higherValueThan(PokerHand h) {
		
		
		return getHandValue() > h.getHandValue(); 
	}

	public String toString() {
	  
		String handString = "";
	  
		for (int x = 0 ; x < hand.length ; x++) {
			handString = hand[x].toString()+", ";
		}
	  
		return handString;
	}

	public int hashCode() {
	  
		int CODE = 0;
		return CODE;
	  
	}

	public boolean equals(Object o) {
		
		return false;
	}
  
}
  
 