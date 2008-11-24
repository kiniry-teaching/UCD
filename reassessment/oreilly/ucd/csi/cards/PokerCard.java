/*
 * UCD CSI Playing Card System.
 * $Id: PokerCard.java 1096 2005-08-24 23:02:36Z jkiniry $
 */

package ie.ucd.csi.cards;


/**
 * A standard playing card.
 *
 * @author Joseph Kiniry <joseph.kiniry@ucd.ie />.
 * @revised Naomi O' Reilly.
 */

public class PokerCard implements Card {

/**
* One of the four suits. Heart, club, diamond or spade.
*/
    private byte suit;
    /**
     * The value of a card.
     */
    private byte value;

/**
 *
 * @param suit
 * @param value
 */
    public PokerCard(final byte suit, final byte value) {
       this.suit = suit;
       this.value = value;
    }
/**
 * @return "Suit: " + suit + ", Value: " + value.
 */
    public final String toString() {
       return "Suit: " + suit + ", Value: " + value;
    }

/**
* @bug Card o should in fact be Object o e.g.PokerDeck.
*
* @see java.lang.Object#equals(java.lang.Object)
* @return true iff Object o is a PokerCard and is
* indistinguishable from PokerCard c.
* @ensures true iff o instanceof PokerCard
*  && sameFaceValueAs(c) && sameSuitAs(c).
* @param o.
*/
     public final boolean equals(final Object o) {
       if (o instanceof PokerCard) {
           PokerCard c = (PokerCard) o;
           return sameFaceValueAs(c) && sameSuitAs(c);
           } else {
           return false;
      }
     }

/** The suite of this card.
 * @return suit.
 */
    public final byte suit() {
       return suit;
    }

/**
* Is 's' a valid suite?
*
* @param s
* a value to check to see if it is a valid suite.
* @return true iff 's' is a valid suite.
*
* @ensures \result <==> ( s == CLUB )|
@                       (s == DIAMOND )|
@                       (s == HEART )|
@                       (s == SPADE);
@*/
    public final boolean validSuit(final byte s) {
       return s == CLUB || s == DIAMOND || s == HEART || s == SPADE;
    }

/** The face-value of this card.
* @return value;
*
* @ensures value;
*/
    public final byte value() {
       return value;
    }

/**
* Is 'v' a valid face-value?
*
* @param v
* the value to check to see if it is a valid face-value.
* @return true iff 'v' is a valid face-value.
* @ensures \result <==> (v == ACE )|
@                       (v == TWO )|
@                       (v == THREE )|
@                       (v == FOUR )|
@                       (v == FIVE )|
@                       (v == SIX )|
@                       (v == SEVEN )|
@                       (v == EIGHT )|
@                       (v == NINE )|
@                       (v == TEN )|
@                       (v == JACK )|
@                       (v == QUEEN )|
@                       (v == KING );
     @*/
    public final boolean validValue(final byte v) {
        return v == ACE || v == TWO || v == THREE || v == FOUR || v == FIVE
                || v == SIX || v == SEVEN || v == EIGHT || v == NINE
                || v == TEN || v == JACK || v == QUEEN || v == KING;
    }

/**
* @param card
* the card to compare.
* @return true iff the suite of this card is identical to the suite of
* <code>a_card</code>
* @ensures suit == a_card.suit();
*/
    public final boolean sameSuitAs(final Card card) {
        return suit == card.suit();
    }

/**
* @param card
* the card to compare
* @return true iff the face value of this card is identical to the face
* value of <code>a_card</code>
* @ensures value == a_card.value();
*/
   public final boolean sameFaceValueAs(final Card card) {
       return value == card.value();
   }

/**
* @param card
* the card to compare
* @return true iff the face value of this card is strictly greater than the
* face value of <code>a_card</code>
* @ensures value > a_card.value();
*/
   public final boolean greaterFaceValueThan(final Card card) {
       return value > card.value();
   }

/**
* Whether this card has a greater value than <code>a_card</code> is
* determined by a given card game's rules.
* @param card
* the card to compare
* @return true iff this card has a great value than <code>a_card</code>
* @ensures value > a_card.value();
*/
   public final boolean greaterValueThan(final Card card) {
       return value > card.value();
   }

/**
* Two cards are equivalent if they are indistinguishable in a given card
* game's rules.
* @param card
* the card to compare
* @return true iff this card and <code>a_card</code> are indistinguishable
*
* @requires value == a_card.value()
* @ensures value == a_card.value() && suit == a_card.suit();
*/
   public final boolean equivalentTo(final Card card) {
       return value == card.value() && suit == card.suit();
   }

/**
* @return hash
*
**/
public final int hashCode() {
int hash = suit;
hash <<= 8;
hash |= value;
return hash;
}

/**
* @param card.
*
* @return 0 || 1 || -1.
**/
public final int compareTo(final Card card) {
       if (this.sameFaceValueAs(card)) {
          return 0;
       } else if (this.greaterFaceValueThan(card)) {
          return 1;
       }
        return -1;
   }
}
