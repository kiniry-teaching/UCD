package cashsystem;

/**
 * A record of any transaction performed by a Johnny Card.
 *
 * @author Damian Chojna (damian.chojna@gmail.com)
 * @version 27 April 2009
 */
public class JohnnyTransaction {

  /** Time and date of the transaction. */
  private final /*@ spec_public */ long timestamp;

  /** Amount in the transaction, can be positive or negative. */
  private final /*@ spec_public */ int amount;

  /** A location identifier for the transaction, e.g. a merchant id */
  private final /*@ spec_public */ String location;

  //@ invariant location != null;

  /**
   * Create new transaction.
   */
  /*@
  requires loc != null;
 */
  public JohnnyTransaction(final int value, final String loc, final long time) {
    this.amount = value;
    this.location = loc;
    this.timestamp = time;
  }

  /**
   * @return What is the timestamp of this transaction?
   */
  /*@
    requires true;
    ensures \result == timestamp;
   */
  public/*@ pure */long getTimestamp() {
    return timestamp;
  }

  /**
   * @return What is the amount involved in this transaction?
   */
  /*@
    requires true;
    ensures \result == amount;
   */
  public/*@ pure */int getAmount() {
    return amount;
  }

  /**
   * @return Where was this transaction?
   */
  /*@
    requires true;
    ensures \result == location;
   */
  public/*@ pure */String getLocation() {
    return location;
  }
}
