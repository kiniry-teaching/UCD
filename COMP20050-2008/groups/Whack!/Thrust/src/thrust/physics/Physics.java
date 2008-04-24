/*
2    * A re-implementation of the classic C=64 game 'Thrust'.
3    *
4    * @author "Joe Kiniry (kiniry@acm.org)"
5    * @module "COMP 20050, COMP 30050"
6    * @creation_date "March 2007"
7    * @last_updated_date "April 2008"
8    * @keywords "C=64", "Thrust", "game"
9    */
10  
11  package thrust.physics;
12  
13  /**
14   * Computing the behavior of entities according to physical
15   * simulation in two dimensions.
16   * @author Joe Kiniry (kiniry@acm.org)
17   * @version 2 April 2008
18   */
19  public interface Physics {
20    //@ constraint (* The gravitational constant never changes. *);
21    //@ constraint gravitational_constant() == \old(gravitational_constant());
22  
23    /**
24     * @return What is your acceleration in meters per second squared?
25     */
26    //@ ensures \result.length == 2;
27    /*@ pure @*/ double[] acceleration();
28  
29    /**
30     * @return What is the gravitational constant?
31     */
32    /*@ pure @*/ double gravitational_constant();
33  
34    /**
35     * @return What is your mass in kilograms?
36     */
37    //@ ensures 0 <= \result;
38    /*@ pure @*/ double mass();
39  
40    /**
41     * @return What is your momentum in kilograms*meters per second?
42     */
43    /*@ pure @*/ double momentum();
44  
45    /**
46     * @return What is your orientation in radians?
47     */
48    /*@ pure @*/ double orientation();
49  
50    /**
51     * @return What is your position in meters from the origin?
52     */
53    //@ ensures \result.length == 2;
54    /*@ pure @*/ double[] position();
55  
56    /**
57     * @return What is your velocity in meters per second?
58     */
59    /*@ pure @*/ double[] velocity();
60  
61    /**
62     * @param the_position This is your position.
63     */
64    //@ requires the_position.length == 2;
65    //@ ensures position()[0] == the_position[0];
66    //@ ensures position()[1] == the_position[1];
67    void position(double[] the_position);
68  
69    /**
70     * @param the_orientation This is your orientation.
71     */
72    //@ ensures orientation() == the_orientation;
73    void orientation(double the_orientation);
74  
75    /**
76     * @param the_mass This is your mass.
77     */
78    //@ requires 0 <= the_mass;
79    //@ ensures mass() == the_mass;
80    void mass(double the_mass);
81  
82    /**
83     * @param the_velocity This is your velocity.
84     */
85    //@ requires the_velocity.length == 2;
86    //@ ensures velocity()[0] == the_velocity[0];
87    //@ ensures velocity()[1] == the_velocity[1];
88    void velocity(double[] the_velocity);
89  
90    /**
91     * @param the_acceleration This is your acceleration.
92     */
93    //@ requires the_acceleration.length == 2;
94    //@ ensures acceleration()[0] == the_acceleration[0];
95    //@ ensures acceleration()[1] == the_acceleration[1];
96    void acceleration(double[] the_acceleration);
97  
98    /**
99     * Simulate yourself for this many seconds.
100      * @param some_seconds the number of seconds to simulate.
101      */
102     void simulate(double some_seconds);
103   }