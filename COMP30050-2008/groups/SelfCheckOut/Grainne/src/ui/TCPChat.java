package ui;

//import java.lang.*;
//import java.util.*;
import java.io.*;
import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import java.net.*;

public class TCPChat implements Runnable {
   // Connect status constants
   public final static int NULL = 0;
   public final static int DISCONNECTED = 1;
   public final static int DISCONNECTING = 2;
   public final static int BEGIN_CONNECT = 3;
   public final static int CONNECTED = 4;

   // Other constants
   public final static String statusMessages[] = {
      " Error! Could not connect!", " Disconnected",
      " Disconnecting...", " Connecting...", " Connected"
   };
   public final static TCPChat tcpObj = new TCPChat();
   public final static String END_CHAT_SESSION =
      new Character((char)0).toString(); // Indicates the end of a session

   public static int connectionStatus = DISCONNECTED;
   public static boolean isHost = true;
   public static String statusString = statusMessages[connectionStatus];
   public static StringBuffer toAppend = new StringBuffer("");
   public static StringBuffer toSend = new StringBuffer("");

   // Various GUI components and info
   public static JFrame mainFrame = null;
   public static JTextArea chatText = null;
   public static JTextField chatLine = null;
   public static JPanel statusBar = null;
   public static JTextField statusColor = null;

   
   public static JButton connectButton = null;
   public static JButton disconnectButton = null;

   // TCP Components
   public static ServerSocket hostServer = null;
   public static Socket socket = null;
   public static BufferedReader in = null;
   public static PrintWriter out = null;

   /////////////////////////////////////////////////////////////////

   private static JPanel initOptionsPane() {
      JPanel pane = null;
      ActionAdapter buttonListener = null;

      // Create an options pane
      JPanel optionsPane = new JPanel(new GridLayout(4, 1));

      // IP address input
      pane = new JPanel(new FlowLayout(FlowLayout.RIGHT));
      pane.add(new JLabel("Host IP:"));
   
      optionsPane.add(pane);

      // Port input
      pane = new JPanel(new FlowLayout(FlowLayout.RIGHT));
      pane.add(new JLabel("Port:"));
     
      optionsPane.add(pane);

      // Host/guest option
      buttonListener = new ActionAdapter() {
            public void actionPerformed(ActionEvent e) {
               if (connectionStatus != DISCONNECTED) {
                  changeStatusNTS(NULL, true);
               }
               else {
                  isHost = e.getActionCommand().equals("host");

                  // Cannot supply host IP if host option is chosen
                
               }
            }
         };
     // ButtonGroup bg = new ButtonGroup();
   
      pane = new JPanel(new GridLayout(1, 2));
     
      optionsPane.add(pane);

      // Connect/disconnect buttons
      JPanel buttonPane = new JPanel(new GridLayout(1, 2));
      buttonListener = new ActionAdapter() {
            public void actionPerformed(ActionEvent e) {
               // Request a connection initiation
               if (e.getActionCommand().equals("connect")) {
                  changeStatusNTS(BEGIN_CONNECT, true);
               }
               // Disconnect
               else {
                  changeStatusNTS(DISCONNECTING, true);
               }
            }
         };
      connectButton = new JButton("Connect");
      connectButton.setMnemonic(KeyEvent.VK_C);
      connectButton.setActionCommand("connect");
      connectButton.addActionListener(buttonListener);
      connectButton.setEnabled(true);
      disconnectButton = new JButton("Disconnect");
      disconnectButton.setMnemonic(KeyEvent.VK_D);
      disconnectButton.setActionCommand("disconnect");
      disconnectButton.addActionListener(buttonListener);
      disconnectButton.setEnabled(false);
      buttonPane.add(connectButton);
      buttonPane.add(disconnectButton);
      optionsPane.add(buttonPane);

      return optionsPane;
   }

   /////////////////////////////////////////////////////////////////

   // Initialize all the GUI components and display the frame
   private static void initGUI() {
      // Set up the status bar
    
      statusColor = new JTextField(1);
      statusColor.setBackground(Color.red);
      statusColor.setEditable(false);
      statusBar = new JPanel(new BorderLayout());
      statusBar.add(statusColor, BorderLayout.WEST);
     
      // Set up the options pane
      JPanel optionsPane = initOptionsPane();

      // Set up the chat pane
      JPanel chatPane = new JPanel(new BorderLayout());
      chatText = new JTextArea(10, 20);
      chatText.setLineWrap(true);
      chatText.setEditable(false);
      chatText.setForeground(Color.blue);
      JScrollPane chatTextPane = new JScrollPane(chatText,
         JScrollPane.VERTICAL_SCROLLBAR_ALWAYS,
         JScrollPane.HORIZONTAL_SCROLLBAR_NEVER);
      chatLine = new JTextField();
      chatLine.setEnabled(false);
      chatLine.addActionListener(new ActionAdapter() {
            public void actionPerformed(ActionEvent e) {
               String s = chatLine.getText();
               if (!s.equals("")) {
                  appendToChatBox("OUTGOING: " + s + "\n");
                  chatLine.selectAll();

                  // Send the string
                  sendString(s);
               }
            }
         });
      chatPane.add(chatLine, BorderLayout.SOUTH);
      chatPane.add(chatTextPane, BorderLayout.CENTER);
      chatPane.setPreferredSize(new Dimension(200, 200));

      // Set up the main pane
      JPanel mainPane = new JPanel(new BorderLayout());
      mainPane.add(statusBar, BorderLayout.SOUTH);
      mainPane.add(optionsPane, BorderLayout.WEST);
      mainPane.add(chatPane, BorderLayout.CENTER);

      // Set up the main frame
      mainFrame = new JFrame("Simple TCP Chat");
      mainFrame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
      mainFrame.setContentPane(mainPane);
      mainFrame.setSize(mainFrame.getPreferredSize());
      mainFrame.setLocation(200, 200);
      mainFrame.pack();
      mainFrame.setVisible(true);
   }

   /////////////////////////////////////////////////////////////////

   // The thread-safe way to change the GUI components while
   // changing state
   private static void changeStatusTS(int newConnectStatus, boolean noError) {
      // Change state if valid state
      if (newConnectStatus != NULL) {
         connectionStatus = newConnectStatus;
      }

      // If there is no error, display the appropriate status message
      if (noError) {
         statusString = statusMessages[connectionStatus];
      }
      // Otherwise, display error message
      else {
         statusString = statusMessages[NULL];
      }

      // Call the run() routine (Runnable interface) on the
      // error-handling and GUI-update thread
      SwingUtilities.invokeLater(tcpObj);
   }

   /////////////////////////////////////////////////////////////////

   // The non-thread-safe way to change the GUI components while
   // changing state
   private static void changeStatusNTS(int newConnectStatus, boolean noError) {
      // Change state if valid state
      if (newConnectStatus != NULL) {
         connectionStatus = newConnectStatus;
      }

      // If there is no error, display the appropriate status message
      if (noError) {
         statusString = statusMessages[connectionStatus];
      }
      // Otherwise, display error message
      else {
         statusString = statusMessages[NULL];
      }

      // Call the run() routine (Runnable interface) on the
      // current thread
      tcpObj.run();
   }

   /////////////////////////////////////////////////////////////////

   // Thread-safe way to append to the chat box
   private static void appendToChatBox(String s) {
      synchronized (toAppend) {
         toAppend.append(s);
      }
   }

   /////////////////////////////////////////////////////////////////

   // Add text to send-buffer
   private static void sendString(String s) {
      synchronized (toSend) {
         toSend.append(s + "\n");
      }
   }

   /////////////////////////////////////////////////////////////////

   // Cleanup for disconnect
   private static void cleanUp() {
      try {
         if (hostServer != null) {
            hostServer.close();
            hostServer = null;
         }
      }
      catch (IOException e) { hostServer = null; }

      try {
         if (socket != null) {
            socket.close();
            socket = null;
         }
      }
      catch (IOException e) { socket = null; }

      try {
         if (in != null) {
            in.close();
            in = null;
         }
      }
      catch (IOException e) { in = null; }

      if (out != null) {
         out.close();
         out = null;
      }
   }

   /////////////////////////////////////////////////////////////////

   // Checks the current state and sets the enables/disables
   // accordingly
   public void run() {
      switch (connectionStatus) {
      case DISCONNECTED:
         connectButton.setEnabled(true);
         disconnectButton.setEnabled(false);
        
         chatLine.setText(""); chatLine.setEnabled(false);
         statusColor.setBackground(Color.red);
         break;

      case DISCONNECTING:
         connectButton.setEnabled(false);
         disconnectButton.setEnabled(false);
     
         chatLine.setEnabled(false);
         statusColor.setBackground(Color.orange);
         break;

      case CONNECTED:
         connectButton.setEnabled(false);
         disconnectButton.setEnabled(true);
       ;
         chatLine.setEnabled(true);
         statusColor.setBackground(Color.green);
         break;

      case BEGIN_CONNECT:
         connectButton.setEnabled(false);
         disconnectButton.setEnabled(false);
       
         chatLine.setEnabled(false);
         chatLine.grabFocus();
         statusColor.setBackground(Color.orange);
         break;
      }

      // Make sure that the button/text field states are consistent
      // with the internal states
     
     
      chatText.append(toAppend.toString());
      toAppend.setLength(0);

      mainFrame.repaint();
   }

   /////////////////////////////////////////////////////////////////

   // The main procedure
   public static void main(String args[]) {
      String s;

      initGUI();

      while (true) {
         try { // Poll every ~10 ms
            Thread.sleep(10);
         }
         catch (InterruptedException e) {}
         appendToChatBox("INCOMING: " + "\n");
         switch (connectionStatus) {
         case CONNECTED:
            try {
               // Send data
               if (toSend.length() != 0) {
                  out.print(toSend); out.flush();
                  toSend.setLength(0);
                  changeStatusTS(NULL, true);
               }

               // Receive data
               if (in.ready()) {
                  s = in.readLine();
                  if ((s != null) &&  (s.length() != 0)) {
                     // Check if it is the end of a trasmission
                     if (s.equals(END_CHAT_SESSION)) {
                        changeStatusTS(DISCONNECTING, true);
                     }

                     // Otherwise, receive what text
                     else {
                        appendToChatBox("INCOMING: " + s + "\n");
                        changeStatusTS(NULL, true);
                     }
                  }
               }
            }
            catch (IOException e) {
               cleanUp();
               changeStatusTS(DISCONNECTED, false);
            }
            break;


         default: break; // do nothing
         }
      }
   }
}

////////////////////////////////////////////////////////////////////

// Action adapter for easy event-listener coding
class ActionAdapter implements ActionListener {
   public void actionPerformed(ActionEvent e) {}
}

////////////////////////////////////////////////////////////////////