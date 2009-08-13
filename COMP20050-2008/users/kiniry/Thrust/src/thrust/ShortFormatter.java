/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */
package thrust;

import java.util.logging.Formatter;
import java.util.logging.LogRecord;

/**
 * Private simple formatter for logger when we do
 * not need timestamps or levels.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 2 May 2008
 */
public class ShortFormatter extends Formatter {
  public String format(final LogRecord the_record) {
    return the_record.getMessage() + "\n";
  }
}
