Please follow the following steps in order to run Construct:

1. Ensure that you have Bonjour and Java 1.5+ installed.

2. The hostname property at the end of the construct.properties file should be changed to reflect your IP address or hostname.

3. (OS X 10.4+ users will not need to follow this step). Next, point the first LD_LIBRARY_PATH variable to the location of 
libjdns_sd.so In the file provided, it is located in ~/mDNSResponder-107.6/mDNSPosix/build/prod/. 
Then remove the #s from that line and the next.
 
4. Run Construct: construct.sh or constructNoGUI.sh can be used to start the program.

If you wish to run the software manually, the main method for Construct is located in the ProxyAndConstructGUIMain class,
which can be found in the ie.ucd.srg.construct.main package. Also included in this package are several other files that 
can be used to launch Construct with varying functionality:

ConstructGuiMain - Launches the GUI version of Construct
ConstructNoGuiMain - Launches the GUIless version of Construct
ProxyMain - Launches the proxy needed by sensors and applications to find instances of Construct running on the network
ProxyAndConstructMain - Launches both the Proxy and the GUI version of Construct
ProxyAndConstructNoGUIMain - Launches both the Proxy and GUIless version of Construct

The launch scripts may be copied and edited to point to one of these alternatives if desired.
