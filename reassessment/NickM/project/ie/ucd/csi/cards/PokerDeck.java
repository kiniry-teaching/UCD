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
	public static PokerCard[] deck = new PokerCard[51];
	
	/**
	 * Constructor for the PokerDeck class.
	 * Creates 52 new PokerCard objects, 1 of each value
	 * in each suite.
	 */
	public PokerDeck() {
		// 52 cards ..
		for (int x = 0 ; x < 52 ; x++) {
			// 4 suites..
			for (byte suite = 0 ; suite < 5 ; suite++) {
				// 13 values ..
				for (byte value = -13 ; value < 0 ; value++) {
					
					deck[x] = new PokerCard(suite, value);
					cardsInDeck++;	
				}	
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
		
		PokerCard topCard = deck[cardsInDeck];
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
		
		String deckString  ="";
		for (int x = 0 ; x < 51 ; x++) {
			deckString = deck[x].toString()+"\n";
		}
		return deckString;
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
