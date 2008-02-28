class A {
  int i = 1;

  public static void main(String[] args) {
    B b = new B();
    C c = new C(b);
    System.out.println("Hello, World!");
    System.out.println(args[0] + " " + b.i);
  }
}

class B extends A {
  int i;
}
