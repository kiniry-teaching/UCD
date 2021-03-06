// This file was generated by jmlunit on Fri May 01 16:01:38 BST 2009.

package johnnytest;

import johnnycash.JohnnyTransaction;

/** Automatically-generated test driver for JML and JUnit based
 * testing of JohnnyTransaction. The superclass of this class should be edited
 * to supply test data. However it's best not to edit this class
 * directly; instead use the command
 * <pre>
 *  jmlunit JohnnyTransaction.java
 * </pre>
 * to regenerate this class whenever JohnnyTransaction.java changes.
 */
public class JohnnyTransaction_JML_Test
     extends JohnnyTransaction_JML_TestData
{
    /** Initialize this class. */
    public JohnnyTransaction_JML_Test(java.lang.String name) {
        super(name);
    }

    /** Run the tests. */
    public static void main(java.lang.String[] args) {
        org.jmlspecs.jmlunit.JMLTestRunner.run(suite());
        // You can also use a JUnit test runner such as:
        // junit.textui.TestRunner.run(suite());
    }

    /** Test to see if the code for class JohnnyTransaction
     * has been compiled with runtime assertion checking (i.e., by jmlc).
     * Code that is not compiled with jmlc would not make an effective test,
     * since no assertion checking would be done. */
    public void test$IsRACCompiled() {
        junit.framework.Assert.assertTrue("code for class JohnnyTransaction"
                + " was not compiled with jmlc"
                + " so no assertions will be checked!",
            org.jmlspecs.jmlrac.runtime.JMLChecker.isRACCompiled(JohnnyTransaction.class)
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
        JohnnyTransaction_JML_Test testobj
            = new JohnnyTransaction_JML_Test("JohnnyTransaction_JML_Test");
        junit.framework.TestSuite testsuite = testobj.overallTestSuite();
        // Add instances of Test found by the reflection mechanism.
        testsuite.addTestSuite(JohnnyTransaction_JML_Test.class);
        testobj.addTestSuiteForEachMethod(testsuite);
        return testsuite;
    }

    /** A JUnit test object that can run a single test method.  This
     * is defined as a nested class solely for convenience; it can't
     * be defined once and for all because it must subclass its
     * enclosing class.
     */
    protected static abstract class OneTest extends JohnnyTransaction_JML_Test {

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
     * JohnnyTransaction.  The framework will then run them.
     * @param overallTestSuite$ The suite accumulating all of the tests
     * for this driver class.
     */
    //@ requires overallTestSuite$ != null;
    public void addTestSuiteForEachMethod
        (junit.framework.TestSuite overallTestSuite$)
    {
        try {
            this.addTestSuiteFor$TestJohnnyTransaction(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestGetJohnnyCardId(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestSetJohnnyCardId(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestGetTransactionDate(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestSetTransactionDate(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestGetTransactionAmount(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestSetTransactionAmount(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestGetTerminalId(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
        try {
            this.addTestSuiteFor$TestSetTerminalId(overallTestSuite$);
        } catch (java.lang.Throwable ex) {
            overallTestSuite$.addTest
                (new org.jmlspecs.jmlunit.strategies.ConstructorFailed(ex));
        }
    }

    /** Add tests for the JohnnyTransaction contructor
     * to the overall test suite. */
    private void addTestSuiteFor$TestJohnnyTransaction
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("JohnnyTransaction");
        try {
            methodTests$.addTest
                (new TestJohnnyTransaction());
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the JohnnyTransaction contructor. */
    protected static class TestJohnnyTransaction extends OneTest {

        /** Initialize this instance. */
        public TestJohnnyTransaction() {
            super("JohnnyTransaction");
        }

        protected void doCall() throws java.lang.Throwable {
            new JohnnyTransaction();
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tContructor 'JohnnyTransaction'";
            return msg;
        }
    }

    /** Add tests for the getJohnnyCardId method
     * to the overall test suite. */
    private void addTestSuiteFor$TestGetJohnnyCardId
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("getJohnnyCardId");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vjohnnycash_JohnnyTransactionIter("getJohnnyCardId", 0));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vjohnnycash_JohnnyTransactionIter(\"getJohnnyCardId\", 0))");
            while (!receivers$iter.atEnd()) {
                final johnnycash.JohnnyTransaction receiver$
                    = (johnnycash.JohnnyTransaction) receivers$iter.get();
                methodTests$.addTest
                    (new TestGetJohnnyCardId(receiver$));
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the getJohnnyCardId method. */
    protected static class TestGetJohnnyCardId extends OneTest {
        /** The receiver */
        private johnnycash.JohnnyTransaction receiver$;

        /** Initialize this instance. */
        public TestGetJohnnyCardId(johnnycash.JohnnyTransaction receiver$) {
            super("getJohnnyCardId");
            this.receiver$ = receiver$;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.getJohnnyCardId();
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'getJohnnyCardId' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            return msg;
        }
    }

    /** Add tests for the setJohnnyCardId method
     * to the overall test suite. */
    private void addTestSuiteFor$TestSetJohnnyCardId
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("setJohnnyCardId");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vjohnnycash_JohnnyTransactionIter("setJohnnyCardId", 1));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vjohnnycash_JohnnyTransactionIter(\"setJohnnyCardId\", 1))");
            while (!receivers$iter.atEnd()) {
                org.jmlspecs.jmlunit.strategies.IntIterator
                    vint$1$iter
                    = this.vintIter("setJohnnyCardId", 0);
                this.check_has_data
                    (vint$1$iter,
                     "this.vintIter(\"setJohnnyCardId\", 0)");
                while (!vint$1$iter.atEnd()) {
                    final johnnycash.JohnnyTransaction receiver$
                        = (johnnycash.JohnnyTransaction) receivers$iter.get();
                    final int theJohnnyCardId
                        = vint$1$iter.getInt();
                    methodTests$.addTest
                        (new TestSetJohnnyCardId(receiver$, theJohnnyCardId));
                    vint$1$iter.advance();
                }
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the setJohnnyCardId method. */
    protected static class TestSetJohnnyCardId extends OneTest {
        /** The receiver */
        private johnnycash.JohnnyTransaction receiver$;
        /** Argument theJohnnyCardId */
        private int theJohnnyCardId;

        /** Initialize this instance. */
        public TestSetJohnnyCardId(johnnycash.JohnnyTransaction receiver$, int theJohnnyCardId) {
            super("setJohnnyCardId"+ ":" + theJohnnyCardId);
            this.receiver$ = receiver$;
            this.theJohnnyCardId = theJohnnyCardId;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.setJohnnyCardId(theJohnnyCardId);
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'setJohnnyCardId' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            msg += "\n\tArgument theJohnnyCardId: " + this.theJohnnyCardId;
            return msg;
        }
    }

    /** Add tests for the getTransactionDate method
     * to the overall test suite. */
    private void addTestSuiteFor$TestGetTransactionDate
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("getTransactionDate");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vjohnnycash_JohnnyTransactionIter("getTransactionDate", 0));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vjohnnycash_JohnnyTransactionIter(\"getTransactionDate\", 0))");
            while (!receivers$iter.atEnd()) {
                final johnnycash.JohnnyTransaction receiver$
                    = (johnnycash.JohnnyTransaction) receivers$iter.get();
                methodTests$.addTest
                    (new TestGetTransactionDate(receiver$));
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the getTransactionDate method. */
    protected static class TestGetTransactionDate extends OneTest {
        /** The receiver */
        private johnnycash.JohnnyTransaction receiver$;

        /** Initialize this instance. */
        public TestGetTransactionDate(johnnycash.JohnnyTransaction receiver$) {
            super("getTransactionDate");
            this.receiver$ = receiver$;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.getTransactionDate();
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'getTransactionDate' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            return msg;
        }
    }

    /** Add tests for the setTransactionDate method
     * to the overall test suite. */
    private void addTestSuiteFor$TestSetTransactionDate
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("setTransactionDate");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vjohnnycash_JohnnyTransactionIter("setTransactionDate", 1));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vjohnnycash_JohnnyTransactionIter(\"setTransactionDate\", 1))");
            while (!receivers$iter.atEnd()) {
                org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                    vjava_util_Date$1$iter
                    = this.vjava_util_DateIter("setTransactionDate", 0);
                this.check_has_data
                    (vjava_util_Date$1$iter,
                     "this.vjava_util_DateIter(\"setTransactionDate\", 0)");
                while (!vjava_util_Date$1$iter.atEnd()) {
                    final johnnycash.JohnnyTransaction receiver$
                        = (johnnycash.JohnnyTransaction) receivers$iter.get();
                    final java.util.Date theDate
                        = (java.util.Date) vjava_util_Date$1$iter.get();
                    methodTests$.addTest
                        (new TestSetTransactionDate(receiver$, theDate));
                    vjava_util_Date$1$iter.advance();
                }
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the setTransactionDate method. */
    protected static class TestSetTransactionDate extends OneTest {
        /** The receiver */
        private johnnycash.JohnnyTransaction receiver$;
        /** Argument theDate */
        private java.util.Date theDate;

        /** Initialize this instance. */
        public TestSetTransactionDate(johnnycash.JohnnyTransaction receiver$, java.util.Date theDate) {
            super("setTransactionDate"+ ":" + (theDate==null? "null" :"{java.util.Date}"));
            this.receiver$ = receiver$;
            this.theDate = theDate;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.setTransactionDate(theDate);
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'setTransactionDate' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            msg += "\n\tArgument theDate: " + this.theDate;
            return msg;
        }
    }

    /** Add tests for the getTransactionAmount method
     * to the overall test suite. */
    private void addTestSuiteFor$TestGetTransactionAmount
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("getTransactionAmount");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vjohnnycash_JohnnyTransactionIter("getTransactionAmount", 0));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vjohnnycash_JohnnyTransactionIter(\"getTransactionAmount\", 0))");
            while (!receivers$iter.atEnd()) {
                final johnnycash.JohnnyTransaction receiver$
                    = (johnnycash.JohnnyTransaction) receivers$iter.get();
                methodTests$.addTest
                    (new TestGetTransactionAmount(receiver$));
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the getTransactionAmount method. */
    protected static class TestGetTransactionAmount extends OneTest {
        /** The receiver */
        private johnnycash.JohnnyTransaction receiver$;

        /** Initialize this instance. */
        public TestGetTransactionAmount(johnnycash.JohnnyTransaction receiver$) {
            super("getTransactionAmount");
            this.receiver$ = receiver$;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.getTransactionAmount();
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'getTransactionAmount' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            return msg;
        }
    }

    /** Add tests for the setTransactionAmount method
     * to the overall test suite. */
    private void addTestSuiteFor$TestSetTransactionAmount
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("setTransactionAmount");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vjohnnycash_JohnnyTransactionIter("setTransactionAmount", 1));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vjohnnycash_JohnnyTransactionIter(\"setTransactionAmount\", 1))");
            while (!receivers$iter.atEnd()) {
                org.jmlspecs.jmlunit.strategies.IntIterator
                    vint$1$iter
                    = this.vintIter("setTransactionAmount", 0);
                this.check_has_data
                    (vint$1$iter,
                     "this.vintIter(\"setTransactionAmount\", 0)");
                while (!vint$1$iter.atEnd()) {
                    final johnnycash.JohnnyTransaction receiver$
                        = (johnnycash.JohnnyTransaction) receivers$iter.get();
                    final int theAmount
                        = vint$1$iter.getInt();
                    methodTests$.addTest
                        (new TestSetTransactionAmount(receiver$, theAmount));
                    vint$1$iter.advance();
                }
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the setTransactionAmount method. */
    protected static class TestSetTransactionAmount extends OneTest {
        /** The receiver */
        private johnnycash.JohnnyTransaction receiver$;
        /** Argument theAmount */
        private int theAmount;

        /** Initialize this instance. */
        public TestSetTransactionAmount(johnnycash.JohnnyTransaction receiver$, int theAmount) {
            super("setTransactionAmount"+ ":" + theAmount);
            this.receiver$ = receiver$;
            this.theAmount = theAmount;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.setTransactionAmount(theAmount);
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'setTransactionAmount' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            msg += "\n\tArgument theAmount: " + this.theAmount;
            return msg;
        }
    }

    /** Add tests for the getTerminalId method
     * to the overall test suite. */
    private void addTestSuiteFor$TestGetTerminalId
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("getTerminalId");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vjohnnycash_JohnnyTransactionIter("getTerminalId", 0));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vjohnnycash_JohnnyTransactionIter(\"getTerminalId\", 0))");
            while (!receivers$iter.atEnd()) {
                final johnnycash.JohnnyTransaction receiver$
                    = (johnnycash.JohnnyTransaction) receivers$iter.get();
                methodTests$.addTest
                    (new TestGetTerminalId(receiver$));
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the getTerminalId method. */
    protected static class TestGetTerminalId extends OneTest {
        /** The receiver */
        private johnnycash.JohnnyTransaction receiver$;

        /** Initialize this instance. */
        public TestGetTerminalId(johnnycash.JohnnyTransaction receiver$) {
            super("getTerminalId");
            this.receiver$ = receiver$;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.getTerminalId();
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'getTerminalId' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            return msg;
        }
    }

    /** Add tests for the setTerminalId method
     * to the overall test suite. */
    private void addTestSuiteFor$TestSetTerminalId
        (junit.framework.TestSuite overallTestSuite$)
    {
        junit.framework.TestSuite methodTests$
            = this.emptyTestSuiteFor("setTerminalId");
        try {
            org.jmlspecs.jmlunit.strategies.IndefiniteIterator
                receivers$iter
                = new org.jmlspecs.jmlunit.strategies.NonNullIteratorDecorator
                    (this.vjohnnycash_JohnnyTransactionIter("setTerminalId", 1));
            this.check_has_data
                (receivers$iter,
                 "new NonNullIteratorDecorator(this.vjohnnycash_JohnnyTransactionIter(\"setTerminalId\", 1))");
            while (!receivers$iter.atEnd()) {
                org.jmlspecs.jmlunit.strategies.IntIterator
                    vint$1$iter
                    = this.vintIter("setTerminalId", 0);
                this.check_has_data
                    (vint$1$iter,
                     "this.vintIter(\"setTerminalId\", 0)");
                while (!vint$1$iter.atEnd()) {
                    final johnnycash.JohnnyTransaction receiver$
                        = (johnnycash.JohnnyTransaction) receivers$iter.get();
                    final int theTerminalId
                        = vint$1$iter.getInt();
                    methodTests$.addTest
                        (new TestSetTerminalId(receiver$, theTerminalId));
                    vint$1$iter.advance();
                }
                receivers$iter.advance();
            }
        } catch (org.jmlspecs.jmlunit.strategies.TestSuiteFullException e$) {
            // methodTests$ doesn't want more tests
        }
        overallTestSuite$.addTest(methodTests$);
    }

    /** Test for the setTerminalId method. */
    protected static class TestSetTerminalId extends OneTest {
        /** The receiver */
        private johnnycash.JohnnyTransaction receiver$;
        /** Argument theTerminalId */
        private int theTerminalId;

        /** Initialize this instance. */
        public TestSetTerminalId(johnnycash.JohnnyTransaction receiver$, int theTerminalId) {
            super("setTerminalId"+ ":" + theTerminalId);
            this.receiver$ = receiver$;
            this.theTerminalId = theTerminalId;
        }

        protected void doCall() throws java.lang.Throwable {
            receiver$.setTerminalId(theTerminalId);
        }

        protected java.lang.String failMessage
            (org.jmlspecs.jmlrac.runtime.JMLAssertionError e$)
        {
            java.lang.String msg = "\n\tMethod 'setTerminalId' applied to";
            msg += "\n\tReceiver: " + this.receiver$;
            msg += "\n\tArgument theTerminalId: " + this.theTerminalId;
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
