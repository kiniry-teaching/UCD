
A.java:

/**

 * A class written for the purpose of making UCD students think hard

 * about build systems. Note carefully the inheritance and the use of

 * the constructor of an instance of the class {@link C}.

 *

 * @author Joe Kiniry

 * @version $Id: A.java,v 1.1 2005/02/08 13:16:04 kiniry Exp $

 */



class A {

 int i = 1;



 /**

 * The main method of our example class. It prints a welcoming

 * message and something about an object.

 *

 * @param args the command-line arguments.

 */

 public static void main(String[] args) {

 B b = new B();

 C c = new C(b);

 System.out.println("Hello, World!");

 System.out.println(args[0] + " " + b.i);

 }

}
