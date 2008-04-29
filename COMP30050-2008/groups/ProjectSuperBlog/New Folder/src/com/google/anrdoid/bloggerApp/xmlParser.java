package com.google.anrdoid.bloggerApp;

import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;


public class xmlParser extends DefaultHandler{

     // ===========================================================
     // Fields
     // ===========================================================
     
     private boolean entry = false;
     private boolean published = false;
     private boolean updated = false;
     private boolean title = false;
     private boolean content = false;
     private boolean author = false;
     private boolean feed = false;
     
     long counter = 0;
     
     int max;
     private ParsedText myParsedTest= new ParsedText();
     // ===========================================================
     // Getter & Setter
     // ===========================================================

         public ParsedText getParsedData() {
         return this.myParsedTest;
     }
     
     // ===========================================================
     // Methods
     // ===========================================================
     
     @Override
     public void startDocument() throws SAXException {
         this.myParsedTest= new ParsedText();
     }

     @Override
     public void endDocument() throws SAXException {
          // Nothing to do
     }

     @Override
     public void startElement(String namespaceURI, String localName,
               String qName, Attributes atts) throws SAXException {
    	// mDbHelper.open(); 
    	 if (localName.equals("entry")) {
               this.entry = true;
      		// myParsedTest.counter(); 
          }else if (localName.equals("published")) {
              this.published = true;
          }else if (localName.equals("updated")) {
              this.updated = true;
          }else if (localName.equals("title")) {
              this.title = true;
          }else if (localName.equals("content")) {
                  this.content = true;
          }else if (localName.equals("author")) {
              this.author = true;
          }else if (localName.equals("feed")) {
              this.feed = true;
          }
     }
     
     @Override
     public void endElement(String namespaceURI, String localName, String qName)
               throws SAXException 
               {
          			if (localName.equals("entry")) 
          			{
          				this.entry = false;
          				myParsedTest.counter();
          			}else if (localName.equals("published")) {
          				this.published = false;
          			}else if (localName.equals("updated")) {
          				this.updated = false;
          			}else if (localName.equals("title")) {
          				this.title = false;
          			}else if (localName.equals("content")) {
          				this.content = false;
          			}else if (localName.equals("author")) {
          				this.author = false;
          			}else if (localName.equals("feed")) {
          				this.feed = false;
          			}
               }

     @Override
    public void characters(char ch[], int start, int length) {
    	 if(this.entry){
    	 }
    	 if(this.published){
    		 myParsedTest.setPublish(new String(ch, start, length));
     }
    	 if(this.updated){
    		 myParsedTest.setUpdate(new String(ch, start, length));
     }
    	 if(this.title){
    		 myParsedTest.setTitle(new String(ch, start, length));
     }
    	 if(this.content){
    		 myParsedTest.setBody(new String(ch, start, length));
     }
    	 if(this.author){
    		 myParsedTest.setAuthor(new String(ch, start, length));
     }
   }
}