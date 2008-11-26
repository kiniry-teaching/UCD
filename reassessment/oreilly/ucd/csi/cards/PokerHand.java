/*
 * UCD CSI Playing Card System.
 * $Id: PokerHand.java 1100 2005-08-24 23:04:23Z jkiniry $
 */

package ie.ucd.csi.cards;

import java.util.Collections;
import java.util.Vector;

/**
 * A five card hand for poker.
 * 
 * @author Joseph Kiniry <joseph.kiniry@ucd.ie />
 * @see http://secure.ucd.ie/~kiniry/part4.txt
 */

public class PokerHand {
	private static final int FIRSTCARD = 0, SECONDCARD = 1, THIRDCARD = 2,
			FOURTHCARD = 3, FIFTHCARD = 4;
	private final byte suit[] = { Card.HEART, Card.SPADE, Card.DIAMOND,
			Card.CLUB };
	private final byte value[] = { Card.ACE, Card.TWO, Card.THREE, Card.FOUR,
			Card.FIVE, Card.SIX, Card.SEVEN, Card.EIGHT, Card.NINE, Card.TEN,
			Card.JACK, Card.QUEEN, Card.KING };
	private byte handValue;
	private Vector<Card> hand;
	/**
	 * The valid Poker hands and their values.
	 */
	public static final byte ROYAL_FLUSH = 1, STRAIGHT_FLUSH = 2,
			FOUR_OF_A_KIND = 3, FULL_HOUSE = 4, FLUSH = 5, STRAIGHT = 6,
			THREE_OF_A_KIND = 7, TWO_PAIRS = 8, ONE_PAIR = 9, HIGH_CARD = 10;

	/**
	 * a Poker Hand.
	 */
	public PokerHand() {
		hand = new Vector<Card>();

	}

	/**
	 * @param c
	 * 
	 * 
	 */
	public void addCard(final Card c) {
		if (hand.size() < 5) {
			hand.add(c);
		}
		if (hand.size() == 5) {
			computePokerHand();
		}

	}

	/**
	 * 
	 * @param c
	 *            .
	 */
	public void removeCard(final Card c) {
		hand.remove(c);
	}

	/**
	 * 
	 * @return count.
	 */
	public final byte count() {
		return (byte) hand.size();
	}

	/**
	 * Is this hand of higher value than the hand 'h'.
	 * 
	 * Recall that in the rules of poker, the order of hand values is as
	 * follows, highest to lowest:
	 * <ol>
	 * 
	 * <li>royal flush</li>, the five highest cards, namely
	 * ace-king-queen-jack-ten of any one of the four suites. The suites have
	 * equal rank. Royal flushes are of equal value.
	 * 
	 * <li>straight flush</li> any five cards of the same suite in numerical
	 * sequence, such as the ten-nine-eight-seven-six of spades. This flush is
	 * called "ten high". Two flushes are compared by comparing their top cards,
	 * e.g., a "ten high" beats a "nine high". If the top cards are the same,
	 * the hands are of equal value.
	 * 
	 * <li>four of a kind</li> any four cards of the same demonination.
	 * 
	 * <li>full house</li> three of one kind and two of another. In evaluating
	 * two full houses, the hand with the highest three of a kind wins.
	 * 
	 * <li>flush</li> any five cards of the same suite, but not in sequence. In
	 * evaluating two flushes, the winner is determined by the rank of the
	 * highest card in the hand. If the highest card is the same, the next
	 * highest cards are compared, etc. If all ranks are equal, the hands are of
	 * equal value.
	 * 
	 * <li>straight</li> five cards in consecutive sequence but not of the same
	 * suite. In competing straights, the winner is decided by the rank of the
	 * highest card. Straights of the same denomination are equal and tie.
	 * 
	 * <li>three of a kind</li> three cards of the same numerical value plus two
	 * different and irrelevant cards. The hand having the highest three of a
	 * kind wins, regardless of the value of the unmatched cards.
	 * 
	 * <li>two pair</li> two different pairs of cards plus one odd card. In
	 * evaluating two two-pair hands, the winner is the hand with the highest
	 * pair. If the highest pairs are tied, the rank of the second pair in the
	 * hands determines the winner. If the second pair is also tied, the higher
	 * card of the odd cards determines the winner. If all cards of the
	 * competing hands are of matching value, the hands are tied.
	 * 
	 * <li>one pair</li> two cards of the same denomination plus three
	 * indifferent unmatched cards. The hand with the higher pair wins. If the
	 * pairs have the same value, the highest indifferent card wins, etc. If all
	 * cards match, the hands tie.
	 * 
	 * <li>high card</li> a hand which contains five indifferent cards not of
	 * the same suite, not in sequence, and falling into none of the above
	 * combinations. Between two high card hands, the highest card determines
	 * the winner, etc. If all cards match, the hands tie.
	 * 
	 * </ol>
	 * 
	 * If two hands are of the same type, then the hand with the highest rank
	 * wins.
	 */

	private void computePokerHand() {
		if (isRoyalFlush()) {
			handValue = ROYAL_FLUSH;
		} else if (isStraightFlush()) {
			handValue = STRAIGHT_FLUSH;
		} else if (isFourOfAKind()) {
			handValue = FOUR_OF_A_KIND;
		} else if (isFullHouse()) {
			handValue = FULL_HOUSE;
		} else if (isFlush()) {
			handValue = FLUSH;
		} else if (isStraight()) {
			handValue = STRAIGHT;
		} else if (isThreeOfAKind()) {
			handValue = THREE_OF_A_KIND;
		} else if (isTwoPair()) {
			handValue = TWO_PAIRS;
		} else if (isOnePair()) {
			handValue = ONE_PAIR;
		} else {
			handValue = HIGH_CARD;
		}
	}

	private boolean isRoyalFlush() {
		for (int i = 0; i < suit.length; i++) {
			if (hand.contains(new PokerCard(suit[i], Card.ACE))
					&& hand.contains(new PokerCard(suit[i], Card.KING))
					&& hand.contains(new PokerCard(suit[i], Card.QUEEN))
					&& hand.contains(new PokerCard(suit[i], Card.JACK))
					&& hand.contains(new PokerCard(suit[i], Card.TEN))) {
				return true;
			}
		}
		return false;
	}

	private boolean isStraightFlush() {
		for (int k = 0; k < suit.length; k++) {
			if (hand.contains(new PokerCard(suit[k], Card.TEN))
					&& hand.contains(new PokerCard(suit[k], Card.JACK))
					&& hand.contains(new PokerCard(suit[k], Card.QUEEN))
					&& hand.contains(new PokerCard(suit[k], Card.KING))
					&& hand.contains(new PokerCard(suit[k], Card.ACE))) {
				return true;
			}
		}
		Collections.sort(hand);
		for (int i = 0; i < hand.size() - 1; i++) {
			if (hand.get(i).value() != hand.get(i + 1).value() - 1
					|| !hand.get(i).sameSuitAs(hand.get(i + 1))) {
				return false;
			}
		}
		return true;
	}

	private boolean isFourOfAKind() {
		for (int j = 0; j < value.length; j++) {
			int count = 0;
			for (int i = 0; i < hand.size(); i++) {
				if (hand.get(i).value() == value[j]) {
					count++;
					if (count == 4) {
						return true;
					}
				}
			}

		}
		return false;
	}

	private boolean isFullHouse() {
		Collections.sort(hand);
		if (hand.get(FIRSTCARD) == hand.get(SECONDCARD)
				&& hand.get(FIRSTCARD) == hand.get(THIRDCARD)) {
			if (hand.get(FOURTHCARD) == hand.get(FIFTHCARD)) {
				return true;
			}
		} else if (hand.get(FIRSTCARD) == hand.get(SECONDCARD)) {
			if (hand.get(THIRDCARD) == hand.get(FOURTHCARD)
					&& hand.get(THIRDCARD) == hand.get(FIFTHCARD)) {
				return true;
			}
		}
		return false;
	}

	private boolean isFlush() {
		for (int i = 0; i < hand.size() - 1; i++) {
			if (!hand.get(i).sameSuitAs(hand.get(i + 1))) {
				return false;
			}
		}
		return true;
	}

	private boolean isStraight() {
		Collections.sort(hand);
		if (hand.get(FIRSTCARD).value() == Card.ACE
				&& hand.get(SECONDCARD).value() == Card.TEN
				&& hand.get(THIRDCARD).value() == Card.JACK
				&& hand.get(FOURTHCARD).value() == Card.QUEEN
				&& hand.get(FIFTHCARD).value() == Card.KING) {
			return true;
		}

		for (int i = 0; i < hand.size() - 1; i++) {
			if (hand.get(i).value() != hand.get(i + 1).value() - 1) {
				return false;
			}
		}
		return true;
	}

	private boolean isThreeOfAKind() {
		if (isFullHouse()) {
			return false;
		} else {
			for (int j = 0; j < value.length; j++) {
				int count = 0;
				for (int i = 0; i < hand.size(); i++) {
					if (hand.get(i).value() == value[j]) {
						count++;
						if (count == 3) {
							return true;
						}
					}
				}
			}
		}
		return false;

	}

	private boolean isTwoPair() {
		Collections.sort(hand);
		if (hand.get(FIRSTCARD) == hand.get(SECONDCARD)
				&& hand.get(THIRDCARD) == hand.get(FOURTHCARD)) {
			return true;
		} else if (hand.get(FIRSTCARD) == hand.get(SECONDCARD)
				&& hand.get(FOURTHCARD) == hand.get(FIFTHCARD)) {
			return true;
		} else if (hand.get(SECONDCARD) == hand.get(THIRDCARD)
				&& hand.get(FOURTHCARD) == hand.get(FIFTHCARD)) {
			return true;
		}
		return false;
	}

	private boolean isOnePair() {
		for (int j = 0; j < value.length; j++) {
			int count = 0;
			for (int i = 0; i < hand.size(); i++) {
				if (hand.get(i).value() == value[j]) {
					count++;
					if (count == 2) {
						return true;
					}
				}
			}

		}
		return false;

	}

	/**
	 * @param h
	 * 
	 * @return int.
	 * 
	 * @bug changed from public boolean(PokerHand h).
	 */
	public int compare(PokerHand h) {
		if (handValue > h.handValue) {
			return 1;
		} else if (handValue == h.handValue) {
			return 0;
		} else {
			return -1;
		}
	}

	/**
	 * @see #higherValueThan(PokerHand)
	 * 
	 * @param handValue == h.handValue
	 *            .
	 * 
	 * @return 
	 */
	public final boolean equal(final PokerHand h) {
		if (handValue == h.handValue) {
			return true;
		}
		return false;
	}

	/**
	 * 
	 * @return "" + handValue;
	 */
	public final String toString() {
		return "" + handValue;
	}

	/**
	 * @return handValue
	 */
	public final int hashCode() {
		return handValue;
	}

	/**
	 * 
	 * @param o
	 *            .
	 * 
	 *@return handValue == o.hashCode().
	 */
	public final boolean equals(final Object o) {
		if (o instanceof PokerHand) {
			return handValue == o.hashCode();
		} else {
			return false;
		}
	}
}