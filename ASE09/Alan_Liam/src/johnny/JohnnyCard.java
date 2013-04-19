package johnny;

/*constraint
"Each Johnny Card is associated with exactly one Johnny Bank",
"Each Johnny Card must have a unique ID.",
"Unique ID can not be modified",
"Only accept transactions if unlocked"
*/

/**
 * The Johnny Card is a digital cash card is a digital cash card
 * which uses flash filesystem to store virtual cash for
 * connectionless point-of-sale transactions.
 *
 * @author Alan Cooke
 * @author Liam McManus
 */
public class JohnnyCard {

  /** Maximum balance a JohnnyCard can be allocated.*/
  public static final int MAX_BALANCE = 500;
  /** The number of transacations that are recorded in the history.*/
  public static final int HISTORY_LENGTH = 5;
  /** Used to maintain the state of the card unlocked/locked.*/
  private transient/*@ spec_public @*/ boolean locked;
  /** Unique ID used to distinguish this card from other instances. */
  private final transient/*@ spec_public @*/ int uniqueID;
  /** An array used to store the last X number of transactions.*/
  private transient/*@ spec_public @*/int[] transHistory;
  /** Balance of cash available on the card.*/
  private transient/*@ spec_public @*/int cash;
  /** The ID of the bank to which the card is associated.*/
  private final transient/*@ spec_public @*/ int bank;

  //@ invariant 0 <= cash && cash <= MAX_BALANCE;
  //@ invariant transHistory.length == HISTORY_LENGTH;
  //@ invariant transHistory != null;
  //@ invariant uniqueID >= 0;

  /*
   *@ requires bankAccNo >= 0 && cardId >= 0;
      ensures !isLocked() &&
              getUniqueID() == cardId && getUniqueID() >= 0 &&
              getCash() == 0 &&
              getBank() >= 0 &&
              transHistory != null &&
              transHistory.length == JohnnyCard.HISTORY_LENGTH &&
             (\forall int i; 0 <= i && i < transHistory.length;
                0 == transHistory[i]);
   */
  /**
   * Constructor builds an instance of the JohnnyCard.
   * The card is created with a balance of zero and no transaction history
   * @param bankAccNo ID of the bank which this card is associated with
   * @param cardId ID of the newly created card
   */
  public JohnnyCard(final int bankAccNo , final int cardId) {
    this.locked = false;
    uniqueID = cardId;
    this.cash = 0;
    this.bank = bankAccNo;
    transHistory = new int[JohnnyCard.HISTORY_LENGTH];
  } // <== this issue seems to be related to uniqueID

  /** Get the amount of cash available on the JohnnyCard.
   * @return How much cash is on this card
   */
   //@ requires !isLocked() ;
   //@ ensures this.cash == \result ;
   public final /*@ pure @*/int getCash() {
     return this.cash;
   };


    /*@ requires !isLocked();
        ensures (\forall int i; 0 <= i && i < transHistory.length;
        \result[i] == transHistory[i]);
     */
    /** Get a list of the last five transactions.
     * @return What are the last five transactions that
     *          this card was involved in.
     */
    public final /*@ pure @*/int[] getLastFiveTrans() {
      final int[] copyOfArray = new int[HISTORY_LENGTH];
      for (int i = 0; i < this.transHistory.length; i++) {
        copyOfArray[i] = this.transHistory[i];
      }
      return copyOfArray;
    }
    /** Get the status of the card, locked/unlocked.
     * @return Is Johnny Card locked?
     */
     //@ requires true ;
     //@ ensures locked == \result;
    public final /*@ pure @*/ boolean isLocked() {
      return this.locked;
    }
    /** Get the unique id of the card.
     * @return What is the unique ID? */
    //@ requires true;
    //@ ensures uniqueID == \result;
    public final /*@ pure @*/ int getUniqueID() {
      return this.uniqueID;
    }

    /**Get the ID of the bank associated with this card.
     * @return What bank does this cards belong to? */
    //@ requires !isLocked();
    //@ ensures bank == \result;
    public final/*@ pure @*/int getBank() {
      return this.bank;
    }

    /*@ requires amount >= -cash && amount <= MAX_BALANCE - cash &&
                 !isLocked();
       ensures cash == \old(cash) + amount &&
              getLastFiveTrans()[HISTORY_LENGTH-1] == amount;
     */
    /** Change the amount of cash on this card by this much.
     * @param amount the amount to be added/removed to/from the Johnny Card
     */
     public final void update(final int amount) {
       cash += amount;
       this.addTransaction(amount);
     }

     /** Lock this card. */
      //@ requires !isLocked();
      //@ ensures locked == true;
      public final void lock() {
        this.locked = true;
      }
      /** Unlock this card, requires the card
       *  to be locked before state is change.
       */
       //@ requires isLocked() ;
       //@ ensures !isLocked() ;
       public final void unlock() {
         this.locked = false;
       }
       /** Add a transaction to the history.
        *  Each new transaction is stored at the end of the array,
        *  the order is descending in time.
        * @param amount Add transaction to history */
       //@ requires !isLocked();
       //@ ensures getLastFiveTrans()[HISTORY_LENGTH-1] == amount;
       private void addTransaction(final int amount) {
         for (int i = transHistory.length - 1; i > 0; i--) {
           transHistory[i - 1] = transHistory[i];
         }
         transHistory[(transHistory.length - 1)] = amount;
       }
}
