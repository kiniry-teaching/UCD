/*
 * UCD CSI Playing Card System.
 * $Id: PokerDeck.java 1096 2005-08-24 23:02:36Z jkiniry $
 */

package ie.ucd.csi.cards;

import java.util.Collections;
import java.util.Stack;
import java.util.Vector;

/**
 * A standard poker deck of 52 playing cards.
 *
 * @author Joseph Kiniry.
 */
public class PokerDeck {
	private Stack <Card> deck;

/**
 * A Poker Deck.
 */
  public PokerDeck() {
	 deck = new Stack <Card>();
	 final byte suit[] = {Card.HEART, Card.SPADE, Card.DIAMOND, Card.CLUB};
	 final byte value[] = {Card.ACE, Card.TWO, Card.THREE, Card.FOUR, Card.FIVE,
			 Card.SIX, Card.SEVEN, Card.EIGHT, Card.NINE, Card.TEN, Card.JACK, Card.QUEEN,
			 Card.KING};
	 for(int i = 0; i < suit.length; i++){
		 for(int j = 0; j < value.length; j++){
			 deck.add(new PokerCard(suit[i],value[j]));
		 }
	 }
  }

  /**
   * @return byte.
   */
  public final byte count() {
	  return (byte) deck.size();
  }

  /**
   * @return Card.
   */
  public Card getCard() {
	  return deck.pop();
  }

  /**
   *
   */
  public void shuffle() {
	  Collections.shuffle(deck);
  }

  /**
   *
   * @return "Count: " + count;
   */
  public final String toString() {
	  return " ";
 }

  /**
   *
   * @return hash.
   */
  public int hashCode() {
	  return deck.size();
  }

  /**
   *
   * @param o.
   *
   * @return true.
   */
  public final boolean equals(final Object o) {
    if (o instanceof PokerDeck) {
        return deck.size() == ((Vector<Card>) o).size();
    }
    return false;
  }
}