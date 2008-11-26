package ie.ucd.csi.cards;
/**
 * test for poker.
 * @author Naomi
 *
 */
public class Main {

/**
* @param args
*/
   public static void main(String[] args) {
       final byte suit[] = { Card.HEART, Card.SPADE, Card.DIAMOND, Card.CLUB };
       PokerDeck d = new PokerDeck();
       d.shuffle();

       PokerHand h = new PokerHand();
//5 is the number of cards allowed ion a poker hand.
       for (int i = 0; i < 5; i++) {
       Card c = d.getCard();
       System.out.println(c);
       h.addCard(c);

      }
      System.out.println(h);
// check whether isFourOfAKind works.
// PokerHand four = new PokerHand();
// for(int i = 0; i < 5; i++){
// Card hace = new PokerCard(Card.HEART, Card.ACE);
// four.addCard(hace);
// Card dace = new PokerCard(Card.DIAMOND, Card.ACE);
// four.addCard(dace);
// Card cace = new PokerCard(Card.CLUB, Card.ACE);
// four.addCard(cace);
// Card sace = new PokerCard(Card.SPADE, Card.ACE);
// four.addCard(sace);
// four.addCard(d.getCard());
// System.out.println(hace +" " +dace + " " +sace +" " + cace);
// }

// System.out.println(four);
//
// Check for isRoyalFlush
// PokerHand RoyalFlush = new PokerHand();
// Card Ace = new PokerCard(Card.HEART, Card.ACE);
// RoyalFlush.addCard(Ace);
// Card King = new PokerCard(Card.HEART, Card.KING);
// RoyalFlush.addCard(King);
// Card Queen = new PokerCard(Card.HEART, Card.QUEEN);
// RoyalFlush.addCard(Queen);
// Card Jack = new PokerCard(Card.HEART, Card.JACK);
// RoyalFlush.addCard(Jack);
// Card Ten = new PokerCard(Card.HEART, Card.TEN);
// RoyalFlush.addCard(Ten);
// System.out.println(Ace + " " + King +" " + Queen + " " + Jack +
// " " + Ten);
// System.out.println(RoyalFlush);

}

}
