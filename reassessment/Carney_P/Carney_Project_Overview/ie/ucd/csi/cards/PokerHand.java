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

  public static final byte ROYAL_FLUSH, STRAIGHT_FLUSH, 
    FOUR_OF_A_KIND, FULL_HOUSE, FLUSH, STRAIGHT, THREE_OF_A_KIND,
    TWO_PAIRS, ONE_PAIR, HIGH_CARD;

  public PokerHand() {
  }

  public void addCard(Card c) {
  }

  public void removeCard(Card c) {
  }

  public byte count() {
    return 0;
  }

  /**
   * Is this hand of higher value than the hand 'h'.
   *
   * Recall that in the rules of poker, the order of hand values is as
   * follows, highest to lowest:
   * <ol>
   *
   * <li> royal flush </li>, the five highest cards, namely
   * ace-king-queen-jack-ten of any one of the four suites.  The
   * suites have equal rank.  Royal flushes are of equal value.
   *
   * <li> straight flush </li> any five cards of the same suite in
   * numerical sequence, such as the ten-nine-eight-seven-six of
   * spades.  This flush is called "ten high".  Two flushes are
   * compared by comparing their top cards, e.g., a "ten high" beats a
   * "nine high".  If the top cards are the same, the hands are of
   * equal value.
   *
   * <li> four of a kind </li> any four cards of the same
   * demonination.
   *
   * <li> full house </li> three of one kind and two of another.  In
   * evaluating two full houses, the hand with the highest three of a
   * kind wins.
   *
   * <li> flush </li> any five cards of the same suite, but not in
   * sequence.  In evaluating two flushes, the winner is determined by
   * the rank of the highest card in the hand.  If the highest card is
   * the same, the next highest cards are compared, etc.  If all ranks
   * are equal, the hands are of equal value.
   *
   * <li> straight </li> five cards in consecutive sequence but not of
   * the same suite.  In competing straights, the winner is decided by
   * the rank of the highest card.  Straights of the same denomination
   * are equal and tie.
   *
   * <li> three of a kind </li> three cards of the same numerical
   * value plus two different and irrelevant cards.  The hand having
   * the highest three of a kind wins, regardless of the value of the
   * unmatched cards.
   *
   * <li> two pair </li> two different pairs of cards plus one odd
   * card.  In evaluating two two-pair hands, the winner is the hand
   * with the highest pair.  If the highest pairs are tied, the rank
   * of the second pair in the hands determines the winner.  If the
   * second pair is also tied, the higher card of the odd cards
   * determines the winner.  If all cards of the competing hands are
   * of matching value, the hands are tied.
   *
   * <li> one pair </li> two cards of the same denomination plus three
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

  public boolean compare(PokerHand h) {
  }

  /**
   * @see #higherValueThan(PokerHand)
   */
  public boolean equal(PokerHand h) {
  }

  public String toString() {
  }

  public int hashCode() {
  }

  public boolean equals(Object o) {
  }
}