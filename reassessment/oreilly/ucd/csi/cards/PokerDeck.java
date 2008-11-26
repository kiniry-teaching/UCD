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
 * @revised Naomi O' Reilly.
 */
public class PokerDeck {
/**
* PokerDeck.
*/
    private Stack < Card > deck;

/**
 * A Poker Deck.
 */
  public PokerDeck() {
    //"'>' is not followed by whitespace." yet if there is whitespace
    //"'(' is preceded with whitespace."
    deck = new Stack < Card >();
    final byte suit[] = {Card.HEART, Card.SPADE, Card.DIAMOND, Card.CLUB};
    final byte value[] = {Card.ACE, Card.TWO, Card.THREE, Card.FOUR, Card.FIVE,
                      Card.SIX, Card.SEVEN, Card.EIGHT, Card.NINE, Card.TEN,
                      Card.JACK, Card.QUEEN, Card.KING};
     for (int i = 0; i < suit.length; i++) {
         for (int j = 0; j < value.length; j++) {
        	 //cannot follow ; by whitespace or there are trailing spaces.
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
  public final Card getCard() {
    return deck.pop();
  }

  /**
   *
   *Shuffles the deck.
   *
   * @ensures Collections.shuffle(deck);
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
   * @return deck.size().
   */
  public final int hashCode() {
     return deck.size();
  }

  /**
   *
   * @param o.
   *
   * @return true iff deck.size() == ((Vector<Card>) o).size().
   */
  public final boolean equals(final Object o) {
    if (o instanceof PokerDeck) {
        return deck.size() == ((Vector<Card> ) o).size();
    }
    return false;
  }
}