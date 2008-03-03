Please follow the following steps in order to run Construct:

1. Ensure that you have Apples Bonjour and Java 1.5+ installed.

2. The hostname property at the end of the construct.properties file should be changed to reflect your IP address or hostname.

3. Ensure the java.library.path variable contains the location of the bonjour library jdns_lib. This can be achieved by following 
the directions in construct.bat or constructNoGUI.bat. The default value of C:/Windows/System32 is usually correct.
 
4. Run Construct: construct.bat or constructNoGUI.bat can be used to start the program.

If you wish to run the software manually, the main method for Construct is located in the ProxyAndConstructGUIMain class,
which can be found in the org.construct_infrastructure.main package. Also included in this package are several other files that 
can be used to launch Construct with varying functionality:

ConstructGuiMain - Launches the GUIless version of Construct
ConstructNoGuiMain - Launches the GUIless version of Construct
ProxyMain - Launches the proxy needed by sensors and applications to find instances of Construct running on the network
ProxyAndConstructMain - Launches both the Proxy and the GUI version of Construct
ProxyAndConstructNoGUIMain - Launches both the Proxy and GUIless version of Construct

The batch files may be copied and edited to point to one of these alternatives if desired.