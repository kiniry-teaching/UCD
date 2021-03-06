// This file was generated by jmlunit on Sun May 10 22:14:55 BST 2009.

package tests;

import cashsystem.*;

/** Automatically-generated test driver for JML and JUnit based
 * testing of JohnnyRegister. The superclass of this class should be edited
 * to supply test data. However it's best not to edit this class
 * directly; instead use the command
 * <pre>
 *  jmlunit JohnnyRegister.java
 * </pre>
 * to regenerate this class whenever JohnnyRegister.java changes.
 */
public class JohnnyRegister_JML_Test
     extends JohnnyRegister_JML_TestData
{
    /** Initialize this class. */
    public JohnnyRegister_JML_Test(java.lang.String name) {
        super(name);
    }

    /** Run the tests. */
    public static void main(java.lang.String[] args) {
        org.jmlspecs.jmlunit.JMLTestRunner.run(suite());
        // You can also use a JUnit test runner such as:
        // junit.textui.TestRunner.run(suite());
    }

    /** Test to see if the code for class JohnnyRegister
     * has been compiled with runtime assertion checking (i.e., by jmlc).
     * Code that is not compiled with jmlc would not make an effective test,
     * since no assertion checking would be done. */
    public void test$IsRACCompiled() {
        junit.framework.Assert.assertTrue("code for class JohnnyRegister"
                + " was not compiled with jmlc"
                + " so no assertions will be checked!",
            org.jmlspecs.jmlrac.runtime.JMLChecker.isRACCompiled(JohnnyRegister.class)
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
        JohnnyRegister_JML_Test testobj
            = new JohnnyRegister_JML_Test("JohnnyRegister_JML_Test");
        junit.framework.TestSuite testsuite = testobj.overallTestSuite();
        // Add instances of Test found by the reflection mechanism.
        testsuite.addTestSuite(JohnnyRegister_JML_Test.class);
        testobj.addTestSuiteForEachMethod(testsuite);
        return testsuite;
    }

    /** A JUnit test object that can run a single test method.  This
     * is defined as a nested class solely for convenience; it can't
     * be defined once and for all because it must subclass its
     * enclosing class.
     */
    protected static abstract class OneTest extends JohnnyRegister_JML_Test {

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
     * JohnnyRegister.  The framework will then run them.
     * @param overallTestSuite$ The suite accumulating all of the tests
     * for this driver class.
     */
    //@ requires overallTestSuite$ != null;
    public void addTestSuiteForEachMethod
        (junit.framework.TestSuite overallTestSuite$)
    {
        try {
            this.addTestSuiteFor$TestJohnnyRegister(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestGetBalance(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestSetBalance(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestGetTransactions(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestInsertCard(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestRemoveCard(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestChargeCard(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestLodgeToBank(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestCardInserted(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestCardIsLocked(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestGetCardBalance(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
    }

    /** Add tests for the JohnnyRegister contructor
     * to the overall test suite. */
    private void addTestSuiteFor$TestJohnnyRegister
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("JohnnyRegister");
        try {
            org.jmlspecs.jmlunit.strategies.IntIterator
                vint$1$iter
                = this.vintIter("JohnnyRegister", 2);
            this.check_has_data
                (vint$1$iter,
                 "this.vintIter(\"JohnnyRegister\", 2)");
            while (!vint$1$iter.atEnd()) {
                org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                    vjava_lang_String$2$iter
                    = this.vjava_lang_StringIter("JohnnyRegister", 1);
                this.check_has_data
                    (vjava_lang_String$2$iter,
                     "this.vjava_lang_StringIter(\"JohnnyRegister\", 1)");
                while (!vjava_lang_String$2$iter.atEnd()) {
                    org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                        vcashsystem_JohnnyBank$3$iter
                        = this.vcashsystem_JohnnyBankIter("JohnnyRegister", 0);
                    this.check_has_data
                        (vcashsystem_JohnnyBank$3$iter,
                         "this.vcashsystem_JohnnyBankIter(\"JohnnyRegister\", 0)");
                    while (!vcashsystem_JohnnyBank$3$iter.atEnd()) {
                        final int account
                            = vint$1$iter.getInt();
                        final java.lang.String loc
                            = (java.lang.String) vjava_lang_String$2$iter.get();
                        final cashsystem.JohnnyBank bank
                            = (cashsystem.JohnnyBank) vcashsystem_JohnnyBank$3$iter.get();
                        methodTests$.addTest
                            (new TestJohnnyRegister(account, loc, bank));
                        vcashsystem_JohnnyBank$3$iter.advance();
                    }
                    vjava_lang_String$2$iter.advance();
                }
                vint$1$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the JohnnyRegister contructor. */
    protected static class TestJohnnyRegister extends OneTest {
        /** Argument account */
        private int account;
        /** Argument loc */
        private java.lang.String loc;
        /** Argument bank */
        private cashsystem.JohnnyBank bank;

        /** Initialize this instance. */
        public TestJohnnyRegister(int account, java.lang.String loc, cashsystem.JohnnyBank bank) {
            super("JohnnyRegister"+ ":" + account+ "," +(loc==null? "null" :("\""+loc+"\""))+ "," +(bank==null? "null" :"{cashsystem.JohnnyBank}"));
            this.account = account;
            this.loc = loc;
            this.bank = bank;
        }

        protected void doCall() throws java.lang.Throwable {
            new JohnnyRegister(account, loc, bank);
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tContructor 'JohnnyRegister' applied to";
            msg += "\n\tArgument account: " + this.account;
            msg += "\n\tArgument loc: " + this.loc;
            msg += "\n\tArgument bank: " + this.bank;
            return msg;
        }
    }

    /** Add tests for the getBalance method
     * to the overall test suite. */
    private void addTestSuiteFor$TestGetBalance
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("getBalance");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vcashsystem_JohnnyRegisterIter("getBalance", 0));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vcashsystem_JohnnyRegisterIter(\"getBalance\", 0))");
            while (!receivers$iter.atEnd()) {
                final cashsystem.JohnnyRegister receiver$
                    = (cashsystem.JohnnyRegister) receivers$iter.get();
                methodTests$.addTest
                    (new TestGetBalance(receiver$));
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the getBalance method. */
    protected static class TestGetBalance extends OneTest {
        /** The receiver */
        private cashsystem.JohnnyRegister receiver$;

        /** Initialize this instance. */
        public TestGetBalance(cashsystem.JohnnyRegister receiver$) {
            super("getBalance");
            this.receiver$ = receiver$;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.getBalance();
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'getBalance' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            return msg;
        }
    }

    /** Add tests for the setBalance method
     * to the overall test suite. */
    private void addTestSuiteFor$TestSetBalance
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("setBalance");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vcashsystem_JohnnyRegisterIter("setBalance", 1));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vcashsystem_JohnnyRegisterIter(\"setBalance\", 1))");
            while (!receivers$iter.atEnd()) {
                org.jmlspecs.jmlunit.strategies.IntIterator
                    vint$1$iter
                    = this.vintIter("setBalance", 0);
                this.check_has_data
                    (vint$1$iter,
                     "this.vintIter(\"setBalance\", 0)");
                while (!vint$1$iter.atEnd()) {
                    final cashsystem.JohnnyRegister receiver$
                        = (cashsystem.JohnnyRegister) receivers$iter.get();
                    final int amount
                        = vint$1$iter.getInt();
                    methodTests$.addTest
                        (new TestSetBalance(receiver$, amount));
                    vint$1$iter.advance();
                }
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the setBalance method. */
    protected static class TestSetBalance extends OneTest {
        /** The receiver */
        private cashsystem.JohnnyRegister receiver$;
        /** Argument amount */
        private int amount;

        /** Initialize this instance. */
        public TestSetBalance(cashsystem.JohnnyRegister receiver$, int amount) {
            super("setBalance"+ ":" + amount);
            this.receiver$ = receiver$;
            this.amount = amount;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.setBalance(amount);
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'setBalance' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            msg += "\n\tArgument amount: " + this.amount;
            return msg;
        }
    }

    /** Add tests for the getTransactions method
     * to the overall test suite. */
    private void addTestSuiteFor$TestGetTransactions
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("getTransactions");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vcashsystem_JohnnyRegisterIter("getTransactions", 0));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vcashsystem_JohnnyRegisterIter(\"getTransactions\", 0))");
            while (!receivers$iter.atEnd()) {
                final cashsystem.JohnnyRegister receiver$
                    = (cashsystem.JohnnyRegister) receivers$iter.get();
                methodTests$.addTest
                    (new TestGetTransactions(receiver$));
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the getTransactions method. */
    protected static class TestGetTransactions extends OneTest {
        /** The receiver */
        private cashsystem.JohnnyRegister receiver$;

        /** Initialize this instance. */
        public TestGetTransactions(cashsystem.JohnnyRegister receiver$) {
            super("getTransactions");
            this.receiver$ = receiver$;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.getTransactions();
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'getTransactions' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            return msg;
        }
    }

    /** Add tests for the insertCard method
     * to the overall test suite. */
    private void addTestSuiteFor$TestInsertCard
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("insertCard");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vcashsystem_JohnnyRegisterIter("insertCard", 1));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vcashsystem_JohnnyRegisterIter(\"insertCard\", 1))");
            while (!receivers$iter.atEnd()) {
                org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                    vcashsystem_JohnnyCard$1$iter
                    = this.vcashsystem_JohnnyCardIter("insertCard", 0);
                this.check_has_data
                    (vcashsystem_JohnnyCard$1$iter,
                     "this.vcashsystem_JohnnyCardIter(\"insertCard\", 0)");
                while (!vcashsystem_JohnnyCard$1$iter.atEnd()) {
                    final cashsystem.JohnnyRegister receiver$
                        = (cashsystem.JohnnyRegister) receivers$iter.get();
                    final cashsystem.JohnnyCard card
                        = (cashsystem.JohnnyCard) vcashsystem_JohnnyCard$1$iter.get();
                    methodTests$.addTest
                        (new TestInsertCard(receiver$, card));
                    vcashsystem_JohnnyCard$1$iter.advance();
                }
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the insertCard method. */
    protected static class TestInsertCard extends OneTest {
        /** The receiver */
        private cashsystem.JohnnyRegister receiver$;
        /** Argument card */
        private cashsystem.JohnnyCard card;

        /** Initialize this instance. */
        public TestInsertCard(cashsystem.JohnnyRegister receiver$, cashsystem.JohnnyCard card) {
            super("insertCard"+ ":" + (card==null? "null" :"{cashsystem.JohnnyCard}"));
            this.receiver$ = receiver$;
            this.card = card;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.insertCard(card);
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'insertCard' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            msg += "\n\tArgument card: " + this.card;
            return msg;
        }
    }

    /** Add tests for the removeCard method
     * to the overall test suite. */
    private void addTestSuiteFor$TestRemoveCard
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("removeCard");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vcashsystem_JohnnyRegisterIter("removeCard", 0));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vcashsystem_JohnnyRegisterIter(\"removeCard\", 0))");
            while (!receivers$iter.atEnd()) {
                final cashsystem.JohnnyRegister receiver$
                    = (cashsystem.JohnnyRegister) receivers$iter.get();
                methodTests$.addTest
                    (new TestRemoveCard(receiver$));
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the removeCard method. */
    protected static class TestRemoveCard extends OneTest {
        /** The receiver */
        private cashsystem.JohnnyRegister receiver$;

        /** Initialize this instance. */
        public TestRemoveCard(cashsystem.JohnnyRegister receiver$) {
            super("removeCard");
            this.receiver$ = receiver$;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.removeCard();
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'removeCard' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            return msg;
        }
    }

    /** Add tests for the chargeCard method
     * to the overall test suite. */
    private void addTestSuiteFor$TestChargeCard
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("chargeCard");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vcashsystem_JohnnyRegisterIter("chargeCard", 1));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vcashsystem_JohnnyRegisterIter(\"chargeCard\", 1))");
            while (!receivers$iter.atEnd()) {
                org.jmlspecs.jmlunit.strategies.IntIterator
                    vint$1$iter
                    = this.vintIter("chargeCard", 0);
                this.check_has_data
                    (vint$1$iter,
                     "this.vintIter(\"chargeCard\", 0)");
                while (!vint$1$iter.atEnd()) {
                    final cashsystem.JohnnyRegister receiver$
                        = (cashsystem.JohnnyRegister) receivers$iter.get();
                    final int amount
                        = vint$1$iter.getInt();
                    methodTests$.addTest
                        (new TestChargeCard(receiver$, amount));
                    vint$1$iter.advance();
                }
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the chargeCard method. */
    protected static class TestChargeCard extends OneTest {
        /** The receiver */
        private cashsystem.JohnnyRegister receiver$;
        /** Argument amount */
        private int amount;

        /** Initialize this instance. */
        public TestChargeCard(cashsystem.JohnnyRegister receiver$, int amount) {
            super("chargeCard"+ ":" + amount);
            this.receiver$ = receiver$;
            this.amount = amount;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.chargeCard(amount);
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'chargeCard' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            msg += "\n\tArgument amount: " + this.amount;
            return msg;
        }
    }

    /** Add tests for the lodgeToBank method
     * to the overall test suite. */
    private void addTestSuiteFor$TestLodgeToBank
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("lodgeToBank");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vcashsystem_JohnnyRegisterIter("lodgeToBank", 0));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vcashsystem_JohnnyRegisterIter(\"lodgeToBank\", 0))");
            while (!receivers$iter.atEnd()) {
                final cashsystem.JohnnyRegister receiver$
                    = (cashsystem.JohnnyRegister) receivers$iter.get();
                methodTests$.addTest
                    (new TestLodgeToBank(receiver$));
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the lodgeToBank method. */
    protected static class TestLodgeToBank extends OneTest {
        /** The receiver */
        private cashsystem.JohnnyRegister receiver$;

        /** Initialize this instance. */
        public TestLodgeToBank(cashsystem.JohnnyRegister receiver$) {
            super("lodgeToBank");
            this.receiver$ = receiver$;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.lodgeToBank();
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'lodgeToBank' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            return msg;
        }
    }

    /** Add tests for the cardInserted method
     * to the overall test suite. */
    private void addTestSuiteFor$TestCardInserted
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("cardInserted");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vcashsystem_JohnnyRegisterIter("cardInserted", 0));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vcashsystem_JohnnyRegisterIter(\"cardInserted\", 0))");
            while (!receivers$iter.atEnd()) {
                final cashsystem.JohnnyRegister receiver$
                    = (cashsystem.JohnnyRegister) receivers$iter.get();
                methodTests$.addTest
                    (new TestCardInserted(receiver$));
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the cardInserted method. */
    protected static class TestCardInserted extends OneTest {
        /** The receiver */
        private cashsystem.JohnnyRegister receiver$;

        /** Initialize this instance. */
        public TestCardInserted(cashsystem.JohnnyRegister receiver$) {
            super("cardInserted");
            this.receiver$ = receiver$;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.cardInserted();
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'cardInserted' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            return msg;
        }
    }

    /** Add tests for the cardIsLocked method
     * to the overall test suite. */
    private void addTestSuiteFor$TestCardIsLocked
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("cardIsLocked");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vcashsystem_JohnnyRegisterIter("cardIsLocked", 0));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vcashsystem_JohnnyRegisterIter(\"cardIsLocked\", 0))");
            while (!receivers$iter.atEnd()) {
                final cashsystem.JohnnyRegister receiver$
                    = (cashsystem.JohnnyRegister) receivers$iter.get();
                methodTests$.addTest
                    (new TestCardIsLocked(receiver$));
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the cardIsLocked method. */
    protected static class TestCardIsLocked extends OneTest {
        /** The receiver */
        private cashsystem.JohnnyRegister receiver$;

        /** Initialize this instance. */
        public TestCardIsLocked(cashsystem.JohnnyRegister receiver$) {
            super("cardIsLocked");
            this.receiver$ = receiver$;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.cardIsLocked();
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'cardIsLocked' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            return msg;
        }
    }

    /** Add tests for the getCardBalance method
     * to the overall test suite. */
    private void addTestSuiteFor$TestGetCardBalance
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("getCardBalance");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vcashsystem_JohnnyRegisterIter("getCardBalance", 0));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vcashsystem_JohnnyRegisterIter(\"getCardBalance\", 0))");
            while (!receivers$iter.atEnd()) {
                final cashsystem.JohnnyRegister receiver$
                    = (cashsystem.JohnnyRegister) receivers$iter.get();
                methodTests$.addTest
                    (new TestGetCardBalance(receiver$));
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the getCardBalance method. */
    protected static class TestGetCardBalance extends OneTest {
        /** The receiver */
        private cashsystem.JohnnyRegister receiver$;

        /** Initialize this instance. */
        public TestGetCardBalance(cashsystem.JohnnyRegister receiver$) {
            super("getCardBalance");
            this.receiver$ = receiver$;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.getCardBalance();
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'getCardBalance' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
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
