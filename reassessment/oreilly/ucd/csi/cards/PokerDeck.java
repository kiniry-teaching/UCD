/*
 * UCD CSI Playing Card System.
 * $Id: PokerDeck.java 1096 2005-08-24 23:02:36Z jkiniry $
 */

package ie.ucd.csi.cards;


import java.util.HashSet;
import java.util.Hashtable;
import java.util.SortedMap;
import java.util.SortedSet;
import java.util.TreeSet;

/**
 * A standard poker deck of 52 playing cards.
 *
 * @author Joseph Kiniry.
 */


public class PokerDeck {
/**
 * The number of cards in a deck.
 */
private byte count;
/**
 * A Poker Deck.
 */
  public PokerDeck() {
  }

  /**
   * @return count.
   */
  public final byte count() {
   return count;
  }

  /**
   * @return Card.
   */
  public Card getCard() {

  }

  /**
   *
   */
  public void shuffle() {

  }

  /**
   *
   * @return "Count: " + count;
   */
  public final String toString() {
     return "Count: " + count;
 }

  /**
   *
   * @return hash.
   */
  public int hashCode() {
  }

  /**
   *
   * @param o.
   *
   * @return true.
   */
  public final boolean equals(final Object o) {
    if (o instanceof PokerDeck) {
        return true;
    }
    return false;
  }
}