package niall;

import java.util.Date;

import junit.framework.TestCase;

/**
 * Test the scenarios for the Johnny Cash System.
 *
 * @author Niall
 *
 */
public class ScenarioTest extends TestCase {

	public static final int INIT_CASH = 200;
	public static final int CASH_VALUE = 100;

	/**
	 * Initializes a new card so that it is associated
	 * with an account, contains no cash, is unlocked, and has no transactions.
	 */
	public void testInitializeCard() {
		JohnnyCard card = new JohnnyCard(new JohnnyBank());
		assertNotNull("The card should not be null", card);
		assertNotNull("The account should not be null", card.getBankAccount());
		assertEquals("The card should have no cash", 0, card.getCashBalance());
		assertFalse("The card should be unlocked", card.isLocked());
		assertEquals("The card should have no transactions", 0, card.getTransactions().length);
	}

	/**
	 * Typing an incorrect PIN code three times locks the card so that it cannot
	 * be used in any JOHNNY_TERMINAL or JOHNNY_MACHINE until it is unlocked
	 * by the owner's bank.
	 */
	public void testLockCard() {
		JohnnyCard card = new JohnnyCard(new JohnnyBank());
		JohnnyMachine johnnyMachine = new JohnnyMachine();
		johnnyMachine.initCardSession();
		int goodPin = 9999;
		int badPin = 8888;
		johnnyMachine.validatePin(goodPin, card);
		johnnyMachine.validatePin(badPin, card);
		johnnyMachine.validatePin(badPin, card);
		assertFalse("The card associated with this account should not be locked",
				card.isLocked());
		johnnyMachine.validatePin(badPin, card);
		assertTrue("The card associated with this account should be locked",
				card.isLocked());
	}

	/**
	 * Ask the user if they would like to deduct a specific amount from the card,
	 * if the user says yes then deduct that amount from the card, record the
	 * transaction.
	 */
	public void testPayForItem() {
		JohnnyRegister register = new JohnnyRegister();
		JohnnyCard card = new JohnnyCard(new JohnnyBank());
		card.setLocked(false);
		card.updateCashBalance(INIT_CASH);
		int initialRegisterTransactions = register.getTransactions().length;
		int initialCardTransactions = card.getTransactions().length;
		Date date = new Date();
		register.recordTransaction(card, CASH_VALUE, date);
		// Record two transactions to get full code coverage
		register.recordTransaction(card, CASH_VALUE, date);
		assertEquals("The cash balance is incorrect", card.getCashBalance(),
				INIT_CASH - CASH_VALUE - CASH_VALUE);
		assertEquals("The transaction was not recorded on the register",
				register.getTransactions().length, initialRegisterTransactions + 2);
		assertEquals("The transaction was not recorded on the card",
				card.getTransactions().length, initialCardTransactions + 2);
		JohnnyTrannie transaction = card.getTransactions()[0];
		assertEquals("The amount on the transaction is incorrect", CASH_VALUE, transaction.getAmount());
		assertEquals("The card on the transaction is incorrect", card, transaction.getCard());
		assertEquals("The date on the transaction is incorrect", date, transaction.getDate());
		assertEquals("The transaction type is incorrect", JohnnyTrannie.PURCHASE_TYPE, transaction.getTransactionType());
		JohnnyTrannie registerTransaction = register.getTransactions()[0];
		assertEquals("The register transaction is incorrect", transaction, registerTransaction);
	}

	/**
	 * Ask the user how much cash they would like to add to the card,
	 * check that sufficient funds are available, deduct the cash from the
	 * account, add the cash to the card, record the transaction.
	 */
	public void testIncreaseCashOnCard() {
		JohnnyMachine johnnyMachine = new JohnnyMachine();
		JohnnyBank johnnyBank = new JohnnyBank();
		JohnnyCard johnnyCard = new JohnnyCard(johnnyBank);
		assertTrue(johnnyCard.getCashBalance() == 0);
		final int defaultBalance = johnnyBank.getBalance();
		final int deposit = 50;
		johnnyBank.updateBalance(deposit);
		assertEquals(deposit + defaultBalance, johnnyBank.getBalance());
		int startingBalance = johnnyBank.getBalance();
		final int amountToAddToCard = 20;
		johnnyMachine.transferFunds(johnnyCard, amountToAddToCard);

		int johnnyBankBalance = johnnyMachine.getBalance(johnnyCard);
		int johnnyCardBalance = johnnyMachine.getJohnnyCardBalance(johnnyCard);
		assertTrue(johnnyCardBalance == amountToAddToCard);
		assertTrue(johnnyBankBalance == (startingBalance - amountToAddToCard));
	}
}
