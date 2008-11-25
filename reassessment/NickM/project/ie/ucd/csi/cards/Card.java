/*
 * UCD CSI Playing Card System.
 * $Id: Card.java 1096 2005-08-24 23:02:36Z jkiniry $
 */

package ie.ucd.csi.cards;

/**
 * A playing card.
 *
 * @author Joseph Kiniry <joseph.kiniry@ucd.ie>
 * 
 * @todo kiniry How much of this can be put into an interface, and
 * what benefits and drawbacks are there to such?
 */

public interface Card {

  /** The four suites. */
  public static final byte CLUB = 0, DIAMOND = 1, HEART = 2, SPADE = 2;

  /** The suite of this card. */
  public byte suite();
  
  /** The thirteen standard cards. */
  public static final byte ACE = -1, TWO = -2, THREE = -3, FOUR = -4,
    FIVE = -5, SOX = -6, SEVEN = -7, EIGHT = -8, NINE = -9, TEN = -10,
    JACK = -11, QUEEN = -12, KING = -13;
  
  /** The face-value of this card */
  public byte value();
  
  
  /**
   * Is 's' a valid suite?
   * 
   * @param s a value to check to see if it is a valid suite.
   * @return true if 's' is a valid suite.
   */
  public boolean validSuite(byte s);


  /**
   * Is 'v' a valid face-value?
   * 
   * @param v the value to check to see if it is a valid face-value.
   * @return true iff 'v' is a valid face-value.
   */
  public boolean validValue(byte v);
  
  /**
   * @param a_card the card to compare
   * @return true iff the suite of this card is identical to the suite
   *         of <code>a_card</code>
   */
  public boolean sameSuiteAs(Card a_card);
  
  /**
   * @param a_card the card to compare
   * @return true iff the face value of this card is identical to the 
   *         face value of <code>a_card</code>
   */
  public boolean sameFaceValueAs(Card a_card);
  
  /**
   * @param a_card the card to compare
   * @return true iff the face value of this card is strictly greater than
   *         the face value of <code>a_card</code>
   */
  public boolean greaterFaceValueThan(Card a_card);
  
  /**
   * Whether this card has a greater value than <code>a_card</code> is
   * determined by a given card game's rules.
   *  
   * @param a_card the card to compare
   * @return true iff this card has a great value than <code>a_card</code>
   */
  public boolean greaterValueThan(Card a_card);
  
  /**
   * Two cards are equivalent if they are indistinguishable in a given
   * card game's rules.
   * 
   * @param a_card the card to compare
   * @return true iff this card and <code>a_card</code> are indistinguishable
   */
  public boolean equivalentTo(Card a_card);

}