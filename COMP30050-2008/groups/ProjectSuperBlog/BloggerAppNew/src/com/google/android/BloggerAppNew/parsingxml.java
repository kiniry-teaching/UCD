package com.google.android.BloggerAppNew;

import java.net.Proxy;
import java.net.Socket;
import java.net.SocketAddress;
import java.net.URL;
import java.net.URLConnection;

import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.xml.sax.InputSource;
import org.xml.sax.XMLReader;

import android.app.Activity;
import android.os.Bundle;
import android.util.Log;
import android.widget.TextView;
public class parsingxml extends Activity {
   
   
   
    ///** Called when the activity is first created. */
    //@Override
    public void onCreate(Bundle icicle) {
         super.onCreate(icicle);
         System.setProperty("http.proxyHost"," 129.188.69.100 ");
         System.setProperty("http.proxyPort","1080");
         System.setProperty("http.nonProxyHosts","10.228.97.76");

         /* Create a new TextView to display the parsingresult later. */
         TextView tv = new TextView(this);
         try {
              /* Create a URL we want to load some xml-data from. */
              URL url = new URL("http://10.232.169.99:8080/phone.xml");
                          URLConnection ucon = url.openConnection();
              /* Get a SAXParser from the SAXPArserFactory. */
              SAXParserFactory spf = SAXParserFactory.newInstance();
              SAXParser sp = spf.newSAXParser();

              /* Get the XMLReader of the SAXParser we created. */
              XMLReader xr = sp.getXMLReader();
              /* Create a new ContentHandler and apply it to the XML-Reader*/
              ExampleHandler myExampleHandler = new ExampleHandler();
              xr.setContentHandler(myExampleHandler);
             
              /* Parse the xml-data from our URL. */
              xr.parse(new InputSource(url.openStream()));
              /* Parsing has finished. */

              /* Our ExampleHandler now provides the parsed data to us. */
              ParsedExampleDataSet parsedExampleDataSet =
                                            myExampleHandler.getParsedData();

              /* Set the result to be displayed in our GUI. */
              tv.setText(parsedExampleDataSet.toString());
             
         } catch (Exception e) {
              /* Display any Error to the GUI. */
              tv.setText("Error: " + e.getMessage());
             
         }
         /* Display the TextView. */
         this.setContentView(tv);
    }
}




Java:
package org.anddev.android.parsingxml;

public class ParsedExampleDataSet {
    private String firstname = null;
    private String lastname=null;
    private String Address=null;
    private String Phone=null;
    private String homephone=null;
    private String workphone=null;
    private String mobilephone=null;

    public String getfirstname() {
         return firstname;
    }
    public void setfirstname(String firstname) {
         this.firstname = firstname;
    }
    public String getlastname(){
     return lastname;
     
    }
    public void setlastname(String lastname){
     this.lastname=lastname;
    }
    public String getAddress(){
     return Address;
    }
public void setAddress(String Address){
     this.Address=Address;
}
    public String getPhone(){
     return Phone;
    }
    public void sethomePhone(String homePhone){
     this.homephone=homePhone;
    }
    public void setworkPhone(String homePhone){
     this.homephone=homePhone;
    }
    public void setmobilePhone(String homePhone){
     this.homephone=homePhone;
    }
     
   
    public String toString(){
         return "firstname = " + this.firstname + "\n" + "lastname=" + this.lastname + "\n" + "Address=" + this.Address+ "\n"  + "homephone=" + this.homephone + "\n" + "workphone=" + this.workphone + "\n" + "mobilephone=" + this.mobilephone;
                   
    }
}


ExampleHandler.java:

Java:
package org.anddev.android.parsingxml;

import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;


public class ExampleHandler extends DefaultHandler{

     // ===========================================================
     // Fields
     // ===========================================================
     
     private boolean in_outertag = false;
     private boolean in_innertag = false;
     private boolean in_firstname = false;
     private boolean in_lastname= false;
     private boolean in_Address=false;
     private boolean in_Phone=false;
     private boolean in_homePhone=false;
     private boolean in_workPhone=false;
     private boolean in_mobilePhone=false;
     
     
     private ParsedExampleDataSet myParsedExampleDataSet = new ParsedExampleDataSet();

     // ===========================================================
     // Getter & Setter
     // ===========================================================

     public ParsedExampleDataSet getParsedData() {
          return this.myParsedExampleDataSet;
     }

     // ===========================================================
     // Methods
     // ===========================================================
     //@Override
     public void startDocument() throws SAXException {
          this.myParsedExampleDataSet = new ParsedExampleDataSet();
     }

     //@Override
     public void endDocument() throws SAXException {
          // Nothing to do
     }

     /** Gets be called on opening tags like:
      * <tag>
      * Can provide attribute(s), when xml was like:
      * <tag attribute="attributeValue">*/
    // @Override
     public void startElement(String namespaceURI, String localName,
               String qName, Attributes atts) throws SAXException {
          if (localName.equals("PhoneBook")) {
               this.in_outertag = true;
          }else if (localName.equals("PhonebookEntry")) {
               this.in_innertag = true;
          }else if (localName.equals("firstname")) {
               this.in_firstname = true;
          }else if (localName.equals("lastname"))  {
            this.in_lastname= true;
          }else if(localName.equals("Address"))  {
            this.in_Address= true;
          }else if (localName.equals("Phone")){
           String phoneattr=atts.getValue("loc");
               if(phoneattr.equals("home")){
               this.in_homePhone=true;}
          }else if (localName.equals("Phone")){
            String phoneattr=atts.getValue("loc");
               if(phoneattr.equals("work")){
                this.in_workPhone=true;}
         }else if (localName.equals("Phone")){
           String phoneattr=atts.getValue("loc");
                if(phoneattr.equals("mobile")){
                 this.in_mobilePhone=true;
              }
                      }   
          }
           
            //else if (localName.equals("tagwithnumber")) {
         // }
               // Extract an Attribute
              // String attrValue = atts.getValue("thenumber");
              // int i = Integer.parseInt(attrValue);
              // myParsedExampleDataSet.setExtractedInt(i);
        //  }
     
     
     /** Gets be called on closing tags like:
      * </tag> */
     @Override
     public void endElement(String namespaceURI, String localName, String qName)
               throws SAXException {
          if (localName.equals("Phonebook")) {
               this.in_outertag = false;
          }else if (localName.equals("PhonebookEntry")) {
               this.in_innertag = false;
          }else if (localName.equals("firstname")) {
               this.in_firstname = false;
          }else if (localName.equals("lastname"))  {
            this.in_lastname= false;
          }else if(localName.equals("Address"))  {
            this.in_Address= false;
          }else if(localName.equals("Phone"))   {
            this.in_Phone=false;
          }
     }
     
     /** Gets be called on the following structure:
      * <tag>characters</tag> */
     @Override
    public void characters(char ch[], int start, int length) {
          if(this.in_firstname){
          myParsedExampleDataSet.setfirstname(new String(ch, start, length));
          }
          if(this.in_lastname){
          myParsedExampleDataSet.setlastname(new String(ch, start, length));
          }
          if(this.in_Address){
            myParsedExampleDataSet.setAddress(new String(ch, start, length));
          }
          if(this.in_homePhone){
            myParsedExampleDataSet.sethomePhone(new String(ch, start, length));
          }
          if(this.in_workPhone){
            myParsedExampleDataSet.setworkPhone(new String(ch, start, length));
          }
          if(this.in_mobilePhone){
            myParsedExampleDataSet.setmobilePhone(new String(ch, start, length));
          }
    }
}