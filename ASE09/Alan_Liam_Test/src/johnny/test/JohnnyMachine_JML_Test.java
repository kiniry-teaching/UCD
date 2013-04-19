// This file was generated by jmlunit on Wed May 06 11:02:45 BST 2009.

package johnny.test;

import johnny.JohnnyMachine;

/** Automatically-generated test driver for JML and JUnit based
 * testing of JohnnyMachine. The superclass of this class should be edited
 * to supply test data. However it's best not to edit this class
 * directly; instead use the command
 * <pre>
 *  jmlunit JohnnyMachine.java
 * </pre>
 * to regenerate this class whenever JohnnyMachine.java changes.
 */
public class JohnnyMachine_JML_Test
     extends JohnnyMachine_JML_TestData
{
    /** Initialize this class. */
    public JohnnyMachine_JML_Test(java.lang.String name) {
        super(name);
    }

    /** Run the tests. */
    public static void main(java.lang.String[] args) {
        org.jmlspecs.jmlunit.JMLTestRunner.run(suite());
        // You can also use a JUnit test runner such as:
        // junit.textui.TestRunner.run(suite());
    }

    /** Test to see if the code for class JohnnyMachine
     * has been compiled with runtime assertion checking (i.e., by jmlc).
     * Code that is not compiled with jmlc would not make an effective test,
     * since no assertion checking would be done. */
    public void test$IsRACCompiled() {
        junit.framework.Assert.assertTrue("code for class JohnnyMachine"
                + " was not compiled with jmlc"
                + " so no assertions will be checked!",
            org.jmlspecs.jmlrac.runtime.JMLChecker.isRACCompiled(JohnnyMachine.class)
            );
    }

    /** Return the test suite for this test class.  This will have
    * added to it at least test$IsRACCompiled(), and any test methods
    * written explicitly by the user in the superclass.  It will also
    * have added test suites for each testing each method and
    * constructor.
    */
    //@ ensures \result != null;
    public static junit.framework.Test suite() {
        JohnnyMachine_JML_Test testobj
            = new JohnnyMachine_JML_Test("JohnnyMachine_JML_Test");
        junit.framework.TestSuite testsuite = testobj.overallTestSuite();
        // Add instances of Test found by the reflection mechanism.
        testsuite.addTestSuite(JohnnyMachine_JML_Test.class);
        testobj.addTestSuiteForEachMethod(testsuite);
        return testsuite;
    }

    /** A JUnit test object that can run a single test method.  This
     * is defined as a nested class solely for convenience; it can't
     * be defined once and for all because it must subclass its
     * enclosing class.
     */
    protected static abstract class OneTest extends JohnnyMachine_JML_Test {

        /** Initialize this test object. */
        public OneTest(String name) {
            super(name);
        }

        /** The result object that holds information about testing. */
        protected junit.framework.TestResult result;

        //@ also
        //@ requires result != null;
        public void run(junit.framework.TestResult result) {
            this.result = result;
            super.run(result);
        }

        /* Run a single test and decide whether the test was
         * successful, meaningless, or a failure.  This is the
         * Template Method pattern abstraction of the inner loop in a
         * JML/JUnit test. */
        public void runTest() throws java.lang.Throwable {
            try {
                // The call being tested!
                doCall();
            }
            catch (org.jmlspecs.jmlrac.runtime.JMLEntryPreconditionError e) {
                // meaningless test input
                addMeaningless();
            } catch (org.jmlspecs.jmlrac.runtime.JMLAssertionError e) {
                // test failure
                int l = org.jmlspecs.jmlrac.runtime.JMLChecker.getLevel();
                org.jmlspecs.jmlrac.runtime.JMLChecker.setLevel
                    (org.jmlspecs.jmlrac.runtime.JMLOption.NONE);
                try {
                    java.lang.String failmsg = this.failMessage(e);
                    junit.framework.AssertionFailedError err
                        = new junit.framework.AssertionFailedError(failmsg);
                    err.setStackTrace(new java.lang.StackTraceElement[]{});
                    err.initCause(e);
                    result.addFailure(this, err);
                } finally {
                    org.jmlspecs.jmlrac.runtime.JMLChecker.setLevel(l);
                }
            } catch (java.lang.Throwable e) {
                // test success
            }
        }

        /** Call the method to be tested with the appropriate arguments. */
        protected abstract void doCall() throws java.lang.Throwable;

        /** Format the error message for a test failure, based on the
         * method's arguments. */
        protected abstract java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e);

        /** Inform listeners that a meaningless test was run. */
        private void addMeaningless() {
            if (result instanceof org.jmlspecs.jmlunit.JMLTestResult) {
                ((org.jmlspecs.jmlunit.JMLTestResult)result)
                    .addMeaningless(this);
            }
        }
    }

    /** Create the tests that are to be run for testing the class
     * JohnnyMachine.  The framework will then run them.
     * @param overallTestSuite$ The suite accumulating all of the tests
     * for this driver class.
     */
    //@ requires overallTestSuite$ != null;
    public void addTestSuiteForEachMethod
        (junit.framework.TestSuite overallTestSuite$)
    {
        try {
            this.addTestSuiteFor$TestJohnnyMachine(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestGetCashInBankAccount(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestGetCashOnCard(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestAmmountOfCashToPutOnCard(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestAcceptCard(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestCheckPin(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
    }

    /** Add tests for the JohnnyMachine contructor
     * to the overall test suite. */
    private void addTestSuiteFor$TestJohnnyMachine
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("JohnnyMachine");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                vjohnny_JohnnyBank$_$1$iter
                = this.vjohnny_JohnnyBank$_Iter("JohnnyMachine", 0);
            this.check_has_data
                (vjohnny_JohnnyBank$_$1$iter,
                 "this.vjohnny_JohnnyBank$_Iter(\"JohnnyMachine\", 0)");
            while (!vjohnny_JohnnyBank$_$1$iter.atEnd()) {
                final johnny.JohnnyBank[] banks
                    = (johnny.JohnnyBank[]) vjohnny_JohnnyBank$_$1$iter.get();
                methodTests$.addTest
                    (new TestJohnnyMachine(banks));
                vjohnny_JohnnyBank$_$1$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the JohnnyMachine contructor. */
    protected static class TestJohnnyMachine extends OneTest {
        /** Argument banks */
        private johnny.JohnnyBank[] banks;

        /** Initialize this instance. */
        public TestJohnnyMachine(johnny.JohnnyBank[] banks) {
            super("JohnnyMachine"+ ":" + (banks==null?"null":("{johnny.JohnnyBank["+banks.length + "]"+"}")));
            this.banks = banks;
        }

        protected void doCall() throws java.lang.Throwable {
            new JohnnyMachine(banks);
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tContructor 'JohnnyMachine' applied to";
            msg += "\n\tArgument banks: " + this.banks;
            return msg;
        }
    }

    /** Add tests for the getCashInBankAccount method
     * to the overall test suite. */
    private void addTestSuiteFor$TestGetCashInBankAccount
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("getCashInBankAccount");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vjohnny_JohnnyMachineIter("getCashInBankAccount", 0));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vjohnny_JohnnyMachineIter(\"getCashInBankAccount\", 0))");
            while (!receivers$iter.atEnd()) {
                final johnny.JohnnyMachine receiver$
                    = (johnny.JohnnyMachine) receivers$iter.get();
                methodTests$.addTest
                    (new TestGetCashInBankAccount(receiver$));
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the getCashInBankAccount method. */
    protected static class TestGetCashInBankAccount extends OneTest {
        /** The receiver */
        private johnny.JohnnyMachine receiver$;

        /** Initialize this instance. */
        public TestGetCashInBankAccount(johnny.JohnnyMachine receiver$) {
            super("getCashInBankAccount");
            this.receiver$ = receiver$;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.getCashInBankAccount();
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'getCashInBankAccount' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            return msg;
        }
    }

    /** Add tests for the getCashOnCard method
     * to the overall test suite. */
    private void addTestSuiteFor$TestGetCashOnCard
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("getCashOnCard");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vjohnny_JohnnyMachineIter("getCashOnCard", 0));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vjohnny_JohnnyMachineIter(\"getCashOnCard\", 0))");
            while (!receivers$iter.atEnd()) {
                final johnny.JohnnyMachine receiver$
                    = (johnny.JohnnyMachine) receivers$iter.get();
                methodTests$.addTest
                    (new TestGetCashOnCard(receiver$));
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the getCashOnCard method. */
    protected static class TestGetCashOnCard extends OneTest {
        /** The receiver */
        private johnny.JohnnyMachine receiver$;

        /** Initialize this instance. */
        public TestGetCashOnCard(johnny.JohnnyMachine receiver$) {
            super("getCashOnCard");
            this.receiver$ = receiver$;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.getCashOnCard();
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'getCashOnCard' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            return msg;
        }
    }

    /** Add tests for the ammountOfCashToPutOnCard method
     * to the overall test suite. */
    private void addTestSuiteFor$TestAmmountOfCashToPutOnCard
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("ammountOfCashToPutOnCard");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vjohnny_JohnnyMachineIter("ammountOfCashToPutOnCard", 1));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vjohnny_JohnnyMachineIter(\"ammountOfCashToPutOnCard\", 1))");
            while (!receivers$iter.atEnd()) {
                org.jmlspecs.jmlunit.strategies.IntIterator
                    vint$1$iter
                    = this.vintIter("ammountOfCashToPutOnCard", 0);
                this.check_has_data
                    (vint$1$iter,
                     "this.vintIter(\"ammountOfCashToPutOnCard\", 0)");
                while (!vint$1$iter.atEnd()) {
                    final johnny.JohnnyMachine receiver$
                        = (johnny.JohnnyMachine) receivers$iter.get();
                    final int amount
                        = vint$1$iter.getInt();
                    methodTests$.addTest
                        (new TestAmmountOfCashToPutOnCard(receiver$, amount));
                    vint$1$iter.advance();
                }
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the ammountOfCashToPutOnCard method. */
    protected static class TestAmmountOfCashToPutOnCard extends OneTest {
        /** The receiver */
        private johnny.JohnnyMachine receiver$;
        /** Argument amount */
        private int amount;

        /** Initialize this instance. */
        public TestAmmountOfCashToPutOnCard(johnny.JohnnyMachine receiver$, int amount) {
            super("ammountOfCashToPutOnCard"+ ":" + amount);
            this.receiver$ = receiver$;
            this.amount = amount;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.ammountOfCashToPutOnCard(amount);
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'ammountOfCashToPutOnCard' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            msg += "\n\tArgument amount: " + this.amount;
            return msg;
        }
    }

    /** Add tests for the acceptCard method
     * to the overall test suite. */
    private void addTestSuiteFor$TestAcceptCard
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("acceptCard");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vjohnny_JohnnyMachineIter("acceptCard", 1));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vjohnny_JohnnyMachineIter(\"acceptCard\", 1))");
            while (!receivers$iter.atEnd()) {
                org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                    vjohnny_JohnnyCard$1$iter
                    = this.vjohnny_JohnnyCardIter("acceptCard", 0);
                this.check_has_data
                    (vjohnny_JohnnyCard$1$iter,
                     "this.vjohnny_JohnnyCardIter(\"acceptCard\", 0)");
                while (!vjohnny_JohnnyCard$1$iter.atEnd()) {
                    final johnny.JohnnyMachine receiver$
                        = (johnny.JohnnyMachine) receivers$iter.get();
                    final johnny.JohnnyCard submittedCard
                        = (johnny.JohnnyCard) vjohnny_JohnnyCard$1$iter.get();
                    methodTests$.addTest
                        (new TestAcceptCard(receiver$, submittedCard));
                    vjohnny_JohnnyCard$1$iter.advance();
                }
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the acceptCard method. */
    protected static class TestAcceptCard extends OneTest {
        /** The receiver */
        private johnny.JohnnyMachine receiver$;
        /** Argument submittedCard */
        private johnny.JohnnyCard submittedCard;

        /** Initialize this instance. */
        public TestAcceptCard(johnny.JohnnyMachine receiver$, johnny.JohnnyCard submittedCard) {
            super("acceptCard"+ ":" + (submittedCard==null? "null" :"{johnny.JohnnyCard}"));
            this.receiver$ = receiver$;
            this.submittedCard = submittedCard;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.acceptCard(submittedCard);
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'acceptCard' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            msg += "\n\tArgument submittedCard: " + this.submittedCard;
            return msg;
        }
    }

    /** Add tests for the checkPin method
     * to the overall test suite. */
    private void addTestSuiteFor$TestCheckPin
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("checkPin");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vjohnny_JohnnyMachineIter("checkPin", 1));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vjohnny_JohnnyMachineIter(\"checkPin\", 1))");
            while (!receivers$iter.atEnd()) {
                org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                    vint$_$1$iter
                    = this.vint$_Iter("checkPin", 0);
                this.check_has_data
                    (vint$_$1$iter,
                     "this.vint$_Iter(\"checkPin\", 0)");
                while (!vint$_$1$iter.atEnd()) {
                    final johnny.JohnnyMachine receiver$
                        = (johnny.JohnnyMachine) receivers$iter.get();
                    final int[] pin
                        = (int[]) vint$_$1$iter.get();
                    methodTests$.addTest
                        (new TestCheckPin(receiver$, pin));
                    vint$_$1$iter.advance();
                }
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the checkPin method. */
    protected static class TestCheckPin extends OneTest {
        /** The receiver */
        private johnny.JohnnyMachine receiver$;
        /** Argument pin */
        private int[] pin;

        /** Initialize this instance. */
        public TestCheckPin(johnny.JohnnyMachine receiver$, int[] pin) {
            super("checkPin"+ ":" + (pin==null?"null":("{int["+pin.length + "]"+"}")));
            this.receiver$ = receiver$;
            this.pin = pin;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.checkPin(pin);
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'checkPin' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            msg += "\n\tArgument pin: " + this.pin;
            return msg;
        }
    }

    /** Check that the iterator is non-null and not empty. */
    private void
    check_has_data(org.jmlspecs.jmlunit.strategies.IndefiniteIterator iter,
                   String call)
    {
        if (iter == null) {
            junit.framework.Assert.fail(call + " returned null");
        }
        if (iter.atEnd()) {
            junit.framework.Assert.fail(call + " returned an empty iterator");
        }
    }

    /** Converts a char to a printable String for display */
    public static String charToString(char c) {
        if (c == '\n') {
            return "NL";
        } else if (c == '\r') {
            return "CR";
        } else if (c == '\t') {
            return "TAB";
        } else if (Character.isISOControl(c)) {
            int i = (int)c;
            return "\\u"
                    + Character.forDigit((i/2048)%16,16)
                    + Character.forDigit((i/256)%16,16)
                    + Character.forDigit((i/16)%16,16)
                    + Character.forDigit((i)%16,16);
        }
        return Character.toString(c);
    }
}