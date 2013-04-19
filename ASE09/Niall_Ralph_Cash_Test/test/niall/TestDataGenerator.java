package niall;

import java.util.Calendar;
import java.util.Date;

/**
 * This class is used to supply test data to the unit tests.
 * @author Niall
 * 
 */
public class TestDataGenerator {

	public static JohnnyCard getDefaultCard() {
		return new JohnnyCard(new JohnnyBank());
	}

	public static JohnnyCard getLockedCard() {
		JohnnyCard card = new JohnnyCard(new JohnnyBank());
		card.setLocked(true);
		return card;
	}

	public static JohnnyCard getCardWithCash() {
		JohnnyCard card = new JohnnyCard(new JohnnyBank());
		card.updateCashBalance(200);
		return card;
	}
	
	public static JohnnyTrannie getPurchaseTransaction(){
		return new JohnnyTrannie(new JohnnyCard(new JohnnyBank()), 100, new Date(), JohnnyTrannie.PURCHASE_TYPE);
	}
	
	public static JohnnyTrannie getUploadTransaction(){
		return new JohnnyTrannie(new JohnnyCard(new JohnnyBank()), 300, new Date(), JohnnyTrannie.UPLOAD_TYPE);
	}

	public static int[] getIntRange() {
		return new int[] { -100, -1, 0, 1, 100, 1000, 10000, 9999, 1234 };
	}
	
	public static Date[] getDateRange(){
		Calendar calendar = Calendar.getInstance();
		calendar.set(Calendar.DAY_OF_WEEK, 1);
		return new Date[] {new Date(), calendar.getTime()};
	}
}
