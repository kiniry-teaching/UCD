package email;
import java.awt.*;
//import java.awt.event.*;
//import java.io.*;
//import java.net.*;
//import java.awt.Font;
import javax.swing.*;

public class EmailClient extends JFrame //implements ActionListener
{
	final static boolean shouldFill = true;
    final static boolean shouldWeightX = true;
    final static boolean RIGHT_TO_LEFT = false;
	
	static final long serialVersionUID=0;
    static String customerName;
    static String customerEmail;
    static String ourEmail="info@self-check-out.com";
    static String subject="Your Self Check-out Receipt and Recipes.";
    String messageBodyIntro;
    String recipies;
    String recipeName;
    String recipeOtherIngredients;
    String recipe;
    String receipts;
    String emailBody = messageBodyIntro + receipts + recipies;
    
    JPanel emailPanel = null;
    JTextArea serverReply = new JTextArea();
    JLabel labelServerReply = new JLabel();

    
  
    public static void addComponentsToPane(final Container pane) 
    {
    	GridLayout topLayout = new GridLayout(1,0);
        GridLayout middleLayout = new GridLayout(3,2);
        GridLayout bottomLayout = new GridLayout(2,0);
  
        
        JPanel topPane = new JPanel();
        topPane.setLayout(topLayout);
        JPanel middlePane = new JPanel();
        middlePane.setLayout(middleLayout);
        JPanel bottomPane = new JPanel();
        bottomPane.setLayout(bottomLayout);
       
       
    	
    	JLabel titleLabel = new JLabel("<html><center>Self Check-out Email Client</center></html>");
    	Font f = new Font("Arial",Font.CENTER_BASELINE,14 );
    	titleLabel.setFont(f);
    	topPane.add(titleLabel);
    	//topPane.add(new JSeparator(SwingConstants.HORIZONTAL));
    	
    	
    	JLabel toLabel = new JLabel("To:");
    	JTextField toField = new JTextField();
    	toField.setText(customerEmail);
    	middlePane.add(toLabel);
    	middlePane.add(toField);
    
    
    	
    	JLabel subjectLabel = new JLabel("Subject: ");
    	JTextField subjectField = new JTextField();
    	subjectField.setText("Your self check out receipts and recipies.");
    	middlePane.add(subjectLabel);
    	middlePane.add(subjectField);
    	
    	
    	JLabel fromLabel = new JLabel("From:");
    	JTextField fromField = new JTextField(ourEmail);
    	middlePane.add(fromLabel);
    	middlePane.add(fromField);

    	

        //customerName= getCustomerName();
    	JTextArea messageBodyField = new JTextArea("Dear Thank-you for shopping at the self check-out. " +
    			"Please find your receipts and recipes for your transaction below.");
    	
    	//String introText = "a";
    	//messageBodyField.add(introText, messageBodyField);
    	
    	//messageBodyField.setText("<html>Dear<br> Thank-you for shopping at the self check-out. <br> Please find your receipts and recipes for your transaction below.<br></html>");
    	
    	//("<html>Dear "+customerName+".<br> Thank-you for shopping at the self check-out. <br>" +
		//"Please find your receipts and recipes for your transaction below.</html>");
        //messageBodyIntro = "";
        //messageBodyField.append(messageBodyIntro);
        //receipts = getReceipts();
        //messageBodyField.add(receipts, messageBodyField);
        
        //messageBodyField.add(recipeName, messageBodyField);
    	//messageBodyField.add(recipeOtherIngredients, messageBodyField);
    	//messageBodyField.add(recipe, messageBodyField);
    	
    	
    	
    	JButton sendButton = new JButton("<html><u>Send</u></html>");
    	//sendButton.addActionListener(this);
    	
    	bottomPane.add(messageBodyField);
    	bottomPane.add(sendButton);
    	
    	pane.setSize(500,500);
    	pane.add(topPane, BorderLayout.NORTH);
        pane.add(middlePane, BorderLayout.CENTER);
        pane.add(bottomPane, BorderLayout.SOUTH);
      
    }

    
    
    /**
     * Create the GUI and show it.  For thread safety,
     * this method should be invoked from the
     * event-dispatching thread.
     */
    private static void createAndShowGUI() 
    {
        //Create and set up the window.
        JFrame frame = new JFrame("Self Check Out");
        frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        frame.setSize(500,500);
        frame.setResizable(false);
        //Set up the content pane.
        addComponentsToPane(frame.getContentPane());
       
        //Display the window.
        frame.pack();
        frame.setVisible(true);
    }

    public static void main(String[] args) {
        //Schedule a job for the event-dispatching thread:
        //creating and showing this application's GUI.
        javax.swing.SwingUtilities.invokeLater(new Runnable() {
            public void run() {
                createAndShowGUI();
            }
        });
    }

    /**
    //action listener for send email button
    public void actionPerformed(ActionEvent e)
    {
    	//String mailTo = customerEmail;
        //String mailFrom = ourEmail;
        //String mailMessage = emailBody;
        //String mailSubject = subject;


        //create the request to send to the server
        // Note the "\r\n" indicates a carriage return i.e. the return key
        String request0 = "HELO ucd.ie \r\n";
        String request1 = "MAIL FROM: " + ourEmail + "\r\n";
        String request2 = "RCPT TO:"+ customerEmail + "\r\n";
        String request3 = "DATA \r\n";
        String request4= "From:"+ourEmail+"\r\n";
        String request5= "To:"+customerEmail+"\r\n";
        String request6 = "Subject: " + subject + "\r\n";
        String request7 = emailBody+ "\r\n";
        String request8 = ".\r\n";
        String request9 = "QUIT\r\n";

        try
        {
            //Created TCP Connection to server
            Socket socket = new Socket("mail.ucd.ie", 25);
            DataOutputStream out = new DataOutputStream(socket.getOutputStream());
            BufferedReader in = new BufferedReader(new InputStreamReader(socket.getInputStream()));

           //Read Response from server and prints it out
            String response = getResponse(in);
            System.out.println(response);
            serverReply.append("From server: " +response+"\n");

            //Send request0 - "hello ucd.ie" and prints it out
            out.write(request0.getBytes());
            System.out.println("Client Sent:" + request0);
            //Read Response from server
            String response0 = getResponse(in);
            System.out.println(response0);
            serverReply.append("From server: " +response0+"\n");

            //Send request1 - mail from: and prints it out
            out.write(request1.getBytes());
            System.out.println("Client Sent:" + request1);
            //Read Response from server
            String response1 = getResponse(in);
            System.out.println(response1);
            serverReply.append("From server: " +response1+"\n");


            //Send request2 - mail to: and prints it out
            out.write(request2.getBytes());
            System.out.println("Client Sent:" + request2);
            //Read Response from server
            String response2 = getResponse(in);
            System.out.println(response2);
            serverReply.append("From server: " +response2+"\n");


            //Send request3 - DATA: and prints it out
            out.write(request3.getBytes());
            System.out.println("Client Sent:" + request3);
            //Read Response from server
            String response3 = getResponse(in);
            System.out.println(response3);
            serverReply.append("From server: " +response3+"\n");
            
            //Send request4 - mail to : and prints it out
            out.write(request4.getBytes());
            System.out.println("Client Sent:" + request4);

            //Send request5 - mail from : and prints it out
            out.write(request5.getBytes());
            System.out.println("Client Sent:" + request5);

            //send request6: SUBJECT: and prints it out
            out.write(request6.getBytes());
            System.out.println("Client Sent:" + request6);

            //send request7: MESSAGE: and prints it out
            out.write(request7.getBytes());
            System.out.println("Client Sent:" + request7);


            //Send request8 - "." and prints it out
            out.write(request8.getBytes());
            System.out.println("Client Sent:" + request8);
            //Read Response from server
            String response8 = getResponse(in);
            System.out.println(response8);
            serverReply.append("From server: " +response8);


            //Send request9 - "QUIT" and prints it out
            out.write(request9.getBytes());
            System.out.println("Client Sent:" + request9);
            //Read Response from server
            String response9 = getResponse(in);
            System.out.println(response9);
            serverReply.append("From server: " +response9);


            //Close everything

            out.close();
            in.close();
            socket.close();
        }
        catch(IOException ex1)
        {
        }

    }

    static String getResponse(BufferedReader reader) throws IOException
    {
    	String response = "";
    	String line = reader.readLine();
    	while(reader.ready())
    	{
    		response += line;
    		line = reader.readLine()+"\n";
    	}
    	response +=line;
    	return response;
    }*/

    
}