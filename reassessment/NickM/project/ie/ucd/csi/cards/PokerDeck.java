/*
 * UCD CSI Playing Card System.
 * $Id: PokerDeck.java 1096 2005-08-24 23:02:36Z jkiniry $
 */

package ie.ucd.csi.cards;

import java.util.Random;

/**
 * A standard poker deck of 52 playing cards.
 *
 * @author Joseph Kiniry <joseph.kiniry@ucd.ie>
 */

public class PokerDeck {

	/** 
	 * Variable holding amount of cards CURRENTLY in deck.
	 * i.e. after getCard() method is used, a card is dealt out
	 * from the deck and the cardsInDeck value goes down by 1.
	 */
	public static byte cardsInDeck;
	
	/**
	 * Creates an array of PokerCard objects.
	 */
	public static PokerCard[] deck = new PokerCard[52];
	
	/**
	 * Constructor for the PokerDeck class.
	 * Creates 52 new PokerCard objects, 1 of each value
	 * in each suite.
	 */
	public PokerDeck() {
				
		int x = 0;
		
		// 4 suites..
		for (byte suite = 0 ; suite < 4 ; suite++) {
			// 13 values ..
			for (byte value = 2 ; value < 15 ; value++) {
				
				deck[x] = new PokerCard(suite, value);
				cardsInDeck++;	
				x++;
			}	
		}
	}
	

	/**
	 * @return the amount of cards currently in deck
	 */
	public byte count() {
		return cardsInDeck;
	}
	
	/**
	 * @return Card from the top of the deck.
	 */
	public PokerCard getCard() {
		
		PokerCard topCard = deck[cardsInDeck-1];
		cardsInDeck--;
		return topCard;
	}
	/**
	 * Shuffles the deck.
	 * Fully shuffles deck by exchanging card at every
	 * position with another random card.
	 */
	public void shuffle() {
		
		Random shuffler = new Random();
		
		for (int x = 0 ; x < deck.length ; x++) {
			
			int randomShuffle = shuffler.nextInt(deck.length);
			PokerCard temp = deck[x];
			deck[x] = deck[randomShuffle];
			deck[randomShuffle] = temp;
		}
	}
	
	/**
	 * Returns the deck. In STRING FORM!!!1
	 */
	public String toString() {
		
		String handString = "";
		  
		for (int x = 0 ; x < cardsInDeck ; x++) {
			handString = handString+" "+deck[x].toString()+", ";
		}
	  
		return handString;
	}

	public int hashCode() {
		
		int WHAT = 0;	
		return WHAT;	
	}
	/**
	 * Possible bug?
	 * Why would I want to compare a deck? To another deck..?
	 */
	public boolean equals(Object o) {
		return false;
	}
}
