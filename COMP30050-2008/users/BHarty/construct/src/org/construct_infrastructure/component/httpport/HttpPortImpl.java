//
// $Revision: 7819 $: $Date: 2008-02-21 13:44:31 +0000 (Thu, 21 Feb 2008) $ - $Author: sneely $
//
//  This file is part of Construct, a context-aware systems platform.
//  Copyright (c) 2006, 2007, 2008 UCD Dublin. All rights reserved.
// 
//  Construct is free software; you can redistribute it and/or modify
//  it under the terms of the GNU Lesser General Public License as
//  published by the Free Software Foundation; either version 2.1 of
//  the License, or (at your option) any later version.
// 
//  Construct is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
//  GNU Lesser General Public License for more details.
// 
//  You should have received a copy of the GNU Lesser General Public
//  License along with Construct; if not, write to the Free Software
//  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
//  USA
//
//  Further information about Construct can be obtained from
//  http://www.construct-infrastructure.org
package org.construct_infrastructure.component.httpport;


import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.StringReader;
import java.io.UnsupportedEncodingException;
import java.net.HttpURLConnection;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLDecoder;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Properties;

import org.construct_infrastructure.component.AbstractConstructComponent;
import org.construct_infrastructure.component.datastorage.DataStoreManager;
import org.construct_infrastructure.component.discovery.RegistryService;
import org.construct_infrastructure.componentregistry.ComponentRegistry;
import org.construct_infrastructure.componentregistry.NoSuchComponentException;
import org.construct_infrastructure.io.ServiceComponentDescriptor;
import org.construct_infrastructure.io.ServiceSocket;
import org.construct_infrastructure.loader.ConstructProperties;

import com.hp.hpl.jena.query.QueryException;
import com.hp.hpl.jena.query.QuerySolution;
import com.hp.hpl.jena.query.ResultSet;
import com.hp.hpl.jena.query.ResultSetFactory;
import com.hp.hpl.jena.query.ResultSetFormatter;
import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.ModelFactory;
import com.hp.hpl.jena.rdf.model.RDFNode;
import com.hp.hpl.jena.shared.SyntaxError;

/**
 * The HttpPort accepts HTTP requests of type GET or POST. A GET request will result in the
 * port returning all the data in Construct. A POST request should contain a SPARQL query which
 * will be executed and the results returned.
 * 
 * @author Steve Neely (steve.neely@ucd.ie)
 */
public final class HttpPortImpl extends AbstractConstructComponent implements HttpPort {

   public static final int HTTP_OK = 200;

   public static final int HTTP_BAD_REQUEST = 400;

   public static final int HTTP_FORBIDDEN = 403;

   public static final int HTTP_NOT_FOUND = 404;

   public static final int HTTP_BAD_METHOD = 405;

   public static final int HTTP_SERVER_ERROR = 500;

   public static final String HTTP_OK_REASON_PHRASE = "OK";

   public static final String HTTP_BAD_REQUEST_REASON_PHRASE = "bad request";

   public static final String HTTP_FORBIDDEN_REASON_PHRASE = "forbidden";

   public static final String HTTP_NOT_FOUND_REASON_PHRASE = "not found";

   public static final String HTTP_BAD_METHOD_REASON_PHRASE = "method not supported";

   public static final String HTTP_SERVER_ERROR_REASON_PHRASE = "internal server error";

   public static final String HTML_TEXT_CONTENT_TYPE = "text/html";
   
   public static final String XML_TEXT_CONTENT_TYPE = "text/xml";

   public static final String PLAIN_TEXT_CONTENT_TYPE = "text/plain";
   
   public static final String APPLICATION_XML_CONTENT_TYPE = "application/xml";
   
   public static final String SERVER_IDENTIFIER = "Construct v0.74 HTTP Port";
   
   /**
    * The interface for the data store manager.
    */
   public static final String DSTORE_MANAGER = "org.construct_infrastructure.component"
         + ".datastorage.DataStoreManager";

   /**
    * The interface to the registry service.
    */
   public static final String RSERVICE_MANAGER = "org.construct_infrastructure.component"
         + ".discovery.RegistryService";

   /**
    * The datastore manager that holds a reference to the data store.
    */
   private transient DataStoreManager my_dataStoreManager;

   /**
    * The registry service that holds a reference to the registry service.
    */
   private transient RegistryService my_registryService;

   /**
    * The hostname of this server, which should be in the properties file.
    */
   private String my_hostname = "localhost";
   
   /**
    * The port on which to run this server.
    */
   private int my_port = 0;

   /**
    * The socket that listens for new data submissions.
    */
   private ServiceSocket my_socket;
   
   /**
    * Space where we logically store XSL files. In reality we build a fake 
    * mapping to a local file and send back the real file when a request is 
    * made for our "local" version
    */
   private String my_scratchSpaceForXSLFiles = "/xsl/";

   /**
    * Creates a new Http Port.
    * 
    * @param some_properties
    *           the properties for this component.
    */
   public HttpPortImpl(final Properties some_properties) {
      super();
      setProperties(some_properties);
      my_hostname = (String) ConstructProperties.getHostName();
      if (my_hostname == null) { // if the property hasn't been set then use localhost as last ditch attempt
    	  my_hostname = "localhost";
      }
      startServer();
   }

   /**
    * Start the server listening.
    */
   protected void startServer() {
      final String portProperty = (String) getProperties().get("port");
      my_port = 0; // if we send port 0 to the data port socket it will bind to next
      // available port
      try {
         if (portProperty != null) {
            my_port = Integer.parseInt(portProperty);
         }
         my_socket = new HttpPortSocket(getLogger(), my_port);
         my_port = my_socket.getLocalPort();
         new Thread(my_socket).start();
      } catch (NumberFormatException e) {
         getLogger().warning(
               "Invalid port number specified in properties. Using next available port");
      } catch (IOException e) {
         getLogger().severe("Could not open socket to listen for client requests");
      }
   }

   /**
    * Method takes an HTTP request, decides what type it is (GET, POS, HEAD etc.) and then
    * handles it appropriately. See http://www.w3.org/Protocols/rfc2616/rfc2616-sec5.html
    * 
    * @param the_request
    *           the HTTP request
    * @return the output from handling the request (typically a HTTP header with a bunch of RDF
    *         data) or an error if you send a malformed HTTP request
    */
   public String handleRequest(String the_request) {
      if (the_request.startsWith("GET")) {
         return doGet(the_request);
      } else if (the_request.startsWith("POST")) {
    	  return doPost(the_request);
      } else {
         return getHttpHeader(HTTP_BAD_METHOD, HTML_TEXT_CONTENT_TYPE, 0);
      }
   }

   /**
    * Method that performs the GET request. If there are parameters (i.e.
    * http://[hostname]:[port]/?q=SELECT ?subject ...) this method will attempt to decode them and
    * execute them as a SPAQRL query. If there are no params the we return a query HTML page.
    * 
    * @param the_request
    *           the HTTP GET request to execute
    * @return the output from the request with HTTP header and RDF data
    */
   protected final String doGet(String the_request) {
      String xsl = null;
      StringBuffer response = new StringBuffer();
      String[] request = the_request.split("\r\n"); // split the request header into its separate lines
      request = request[0].split(" "); // we only want the first line with the 3 parts of the GET request. Something like: "GET / HTTP/1.1"
      
      // <URI> <HTTP_VER>
      if (request.length != 3) {
         return getHttpHeader(HTTP_BAD_REQUEST, HTML_TEXT_CONTENT_TYPE, 0);
      }
      // if this is a request for an XSL file we need to extract the real location from the request, GET it and send back
      if (request[1].startsWith(my_scratchSpaceForXSLFiles) && request[1].endsWith(".xsl")) {
         try {
            String urlToXsl = "http://" + request[1].substring(request[1].indexOf(my_scratchSpaceForXSLFiles) + my_scratchSpaceForXSLFiles.length());
            xsl = readFromURL(urlToXsl);
           return getHttpHeader(HTTP_OK, XML_TEXT_CONTENT_TYPE, xsl.length()) + xsl;
         } catch (MalformedURLException mue) {
            String errorMsg = "Request for data at " + request[1].substring(5) + " failed. URL malformed, " + mue.getMessage();
            getLogger().warning(errorMsg);
            return getHttpHeader(HTTP_BAD_REQUEST, HTML_TEXT_CONTENT_TYPE, errorMsg.length()) + errorMsg;
         } catch (IOException ioe) {
            String errorMsg = "Failed to read remote URL: " + ioe.getMessage();
            getLogger().warning(errorMsg);
            return getHttpHeader(HTTP_NOT_FOUND, HTML_TEXT_CONTENT_TYPE, errorMsg.length()) + errorMsg;
         }         
      } else if (request[1].indexOf('?') >= 0) { // is it a query or insert?
    	 String encodedParamsList = request[1].substring(request[1].indexOf('?')+1);
         HashMap<String, String> params = extractURLEncodedParams(encodedParamsList);
         if (params.containsKey("query") || params.containsKey("q")) {
        	 return doQuery(params);
         } else if (params.containsKey("insert") || params.containsKey("i")) {
        	 return doInsert(params);
         } else { // bad query or insert string
      	     response = new StringBuffer(getHtmlForQueryPageAndMalformedQueryError());
    		 return getHttpHeader(HTTP_OK, HTML_TEXT_CONTENT_TYPE, response.length()) + response.toString();
         }
      }
      // default case is to return HTML page for query
      response = new StringBuffer(getHtmlForQueryPage());
      return getHttpHeader(HTTP_OK, HTML_TEXT_CONTENT_TYPE, response.length()) + response.toString();
   }
   /**
    * Method that performs the POST request. If there are parameters (i.e.
    * http://[hostname]:[port]/?q=SELECT ?subject ...) this method will attempt to decode them and
    * execute them as a SPAQRL query. If there are no params the we return a query HTML page.
    * 
    * @param the_request
    *           the HTTP POST request to execute
    * @return the output from the request with HTTP header and RDF data
    */
   protected final String doPost(String the_request) {
      StringBuffer response = new StringBuffer();
      int dataStartsAt = the_request.indexOf("\r\n\r\n")+4; // the marker for the start of the data section is an empty line
      
      // force POST to root only
      if (!the_request.startsWith("POST / ")) {
    	  return getHttpHeader(HTTP_BAD_REQUEST, HTML_TEXT_CONTENT_TYPE, 0);
      }
      if (dataStartsAt > 0) { // if we found a blank line data comes after it
    	  	String encodedParamsList = the_request.substring(dataStartsAt);
         	HashMap<String, String> params = extractURLEncodedParams(encodedParamsList);
         if (params.containsKey("query") || params.containsKey("q")) {
        	 return doQuery(params);
         } else if (params.containsKey("insert") || params.containsKey("i")) {
        	 return doInsert(params);
         } else { // bad query or insert string
      	     response = new StringBuffer(getHtmlForQueryPageAndMalformedQueryError());
    		 return getHttpHeader(HTTP_OK, HTML_TEXT_CONTENT_TYPE, response.length()) + response.toString();
         }
      }
      // default case is to return HTML page for query
      response = new StringBuffer(getHtmlForQueryPage());
      return getHttpHeader(HTTP_OK, HTML_TEXT_CONTENT_TYPE, response.length()) + response.toString();
   }
    
   /**
    * Method that performs a query request. This method expects there are parameters query or q
    * (http://[hostname]:[port]/?q=SELECT ?subject ...), will attempt to decode them and
    * execute them as a SPAQRL query.
    * 
    * @param the_params the map containing the parameters to use
    * @return the output from the request with HTTP header and RDF data
    */
   private final String doQuery(HashMap<String, String> the_params) {
	   StringBuffer response = new StringBuffer();
	   ResultSet resultSet = null;
	   
	   String query = the_params.get("query");
	   String xsl = the_params.get("xsl");
	   
	   if (query == null) {
		   query = the_params.get("q");
	   }
	   if (query == null) {
		   response = new StringBuffer(getHtmlForQueryPageAndMalformedQueryError());
		   return getHttpHeader(HTTP_OK, HTML_TEXT_CONTENT_TYPE, response.length()) + response.toString();
	   }
	   
	   try {
		   String result = my_dataStoreManager.runQuery(query);
		   
		   final Model model = ModelFactory.createDefaultModel();
		   final StringReader modelReader = new StringReader(result);
		   model.read(modelReader, null, "N-TRIPLE");
		   resultSet = ResultSetFactory.fromRDF(model);
	   } catch (QueryException qe) {
		   response = new StringBuffer("<html><head><title>Construct data></title></head><body>Error executing query <tt>"
				   + query + "<br/>" + qe.getMessage() + "</tt></body></html>\n");
           return getHttpHeader(HTTP_OK, HTML_TEXT_CONTENT_TYPE, response.length()) + response.toString();
       }

	   /* To handle XSL we have to cheat a little. We're going to embed a link to the XSL file in the XML generated by the SPARQL query.
	    * Most browsers will refuse to load that XSL unless it is on the same server that returned the XML. To allow people to specify XSL
	    * anywhere on the web we are going to map the real location of the XSL file to a local file (in my_scratchSpaceForXSLFiles) 
	    * and embed that local link in the XML.
	    * 
	    * Back up in the doGet method we'll look for calls to these local XSL file in the "scratch space", load the real XSL from over
	    * the web and send it back. Nasty, but it was either that or copy remote XSL files to this node. All XSL processing happens on the
	    * client so I can't see any security problems with us passing it back.
	    * 
	    */
	   // if there is some xsl we map it to a logically local file for use
	   if (xsl != null && xsl.length() > 0 && xsl.startsWith("http://")) {
		   String localXslUrl = "http://" + my_hostname + ":" + my_port + my_scratchSpaceForXSLFiles + xsl.substring(7);
		   response = new StringBuffer(createXMLFromResultSet(resultSet, localXslUrl));
		   return getHttpHeader(HTTP_OK, APPLICATION_XML_CONTENT_TYPE, response.length()) + response.toString();
       }
          
	   // if we get this far then there was no problems with the query and no associated XSL found so just send back the XML
	   response = new StringBuffer(createXMLFromResultSet(resultSet));
	   return getHttpHeader(HTTP_OK, XML_TEXT_CONTENT_TYPE, response.length()) + response.toString();
   }

   
   /**
    * Method that performs an insert request. This method expects there are parameters insert or i
    * (http://[hostname]:[port]/?i=&lt;subject>&lt;predicate>&lt;object>.), will attempt to decode them and
    * insert them into Construct.
    * 
    * @param the_params
    *           the map containing the parameters to unpack and use
    * @return the output from the request with HTTP header and RDF data
    */
   private final String doInsert(HashMap<String, String> the_params) {
	   String status = null; // the status message for the XML reponse
	   String description = null; // the description message for the XML response
	   StringBuffer response = null;
	   String expiryTime = the_params.get("expiry"); // get (optional) expiry time
	   String insert = the_params.get("insert"); // get data to insert	   

	   if (insert == null) {
		   insert = the_params.get("i"); // param marker for data to insert can also be the letter 'i'
	   }
	   if (insert == null) {
		   response = new StringBuffer(getHtmlForQueryPageAndMalformedQueryError()); // found an "insert" or "i" but no data
		   return getHttpHeader(HTTP_OK, HTML_TEXT_CONTENT_TYPE, response.length()) + response.toString();
	   }
	   
	   try {
		   if (expiryTime == null || expiryTime.equals("")) { // no expiry given so use default
			   my_dataStoreManager.addStatements(insert, "HTTP_PORT");
			   status = "OK";
			   description = "The data " + insert.replaceAll("<", "&lt;") + " was passed to the Construct data store without error.";
		   } else { // expiry time given so check its validity
			   long expiry = -1;
			   try {
				   expiry = Long.parseLong(expiryTime);
				   if (expiry >= 0) { // if the expiry was valid then add it
					   my_dataStoreManager.addStatements(insert, expiry, "HTTP_PORT");
					   status = "OK";
					   description = "The data " + insert.replaceAll("<", "&lt;") + " with given expiry " + expiryTime
					   + " was passed to the Construct data store without error.";
				   }
			   } catch (NumberFormatException nfe) {
				   getLogger().warning("Expiry time " + expiryTime + " passed to HttpPort is not a valid value. Reverting to default.");
				   my_dataStoreManager.addStatements(insert, "HTTP_PORT"); // add data with default expiry time
				   status = "OK";
				   description = "The data " + insert.replaceAll("<", "&lt;")
				   + " was passed to the Construct data store without error." 
				   + " Your expiry time \"" + expiryTime
				   + "\" is not valid so inserted data reverted to the default expiry value.";
			   }
		   }
		   response = new StringBuffer("<response><status>" + status + "</status>"
				   + "<description>" + description + "</description>"
				   + "</response>");
		   return getHttpHeader(HTTP_OK, XML_TEXT_CONTENT_TYPE, response.length()) + response.toString();
	   } catch (SyntaxError se) {
		   status = "ERROR";
		   description = "The data " + insert.replaceAll("<", "&lt;") + " was passed to the Construct data store and caused an error.";
		   response = new StringBuffer("<response><status>" + status + "</status><description>" + description + "</description>"
				   + "<cause>" + se.getCause() + "</cause>"
				   + "<message>" + se.getMessage() + "</message>"
				   + "<localizedMessage>" + se.getLocalizedMessage() + "</localizedMessage>"
				   + "<stackTrace>");
		   for (StackTraceElement stackElem : se.getStackTrace()) {
			   response.append (stackElem + "\n");
		   }
		   response.append("</stackTrace> </response>");
		   return getHttpHeader(HTTP_OK, XML_TEXT_CONTENT_TYPE, response.length()) + response.toString();
	   }
   }


   /**
    * Method that reads data from the given URL
    * @param the_url the URL to read from
    * @return the data at the other end or nothing if the read fails
    */
   protected String readFromURL(String the_url) throws MalformedURLException, IOException {
      StringBuffer response = new StringBuffer();
      HttpURLConnection connection = (HttpURLConnection)(new URL(the_url).openConnection());
      connection.connect();
      if (connection.getResponseCode() != HttpURLConnection.HTTP_OK) {
         getLogger().warning("Failed to open connection to " + the_url + " because "
               + connection.getResponseCode() + " " + connection.getResponseMessage());
         return response.toString();
      }
      BufferedReader in = new BufferedReader(new InputStreamReader(connection.getInputStream()));

      String inputLine;
      
      while ((inputLine = in.readLine()) != null) {
          response.append(inputLine);          
      }
      in.close();
      return response.toString();
   }

   /**
    * Utility method that takes a x-www-form-urlencoded String containing a list of key=value parameters, decodes it, splits key-values, 
    * and returns them in a map. The param string should look something like:
    * 
    * <tt>q=SELECT+%3Fsubject+%3Fpredicate+%3Fobject+WHERE+%7B%3Fsubject+%3Fpredicate+%3Fobject%7D&xsl=http%3A%2F%2Fduvel.ucd.ie%2F%7Esneely%2Fconstruct%2Fdefault.xsl</tt>
    *  
    * @param the_params the param string to split and decode
    * @return the map containing the decoded key-value pairs
    */
   protected HashMap<String, String> extractURLEncodedParams(String the_params) {
	      HashMap<String, String> decodedParams = new HashMap<String, String>();

	      the_params = decodeURLEncodedString(the_params);

	      String[] params = the_params.split("&");
	      for (int i = 0; i < params.length; i++) {
	         int indexOfEqualsOp = params[i].indexOf('=');
	         if (indexOfEqualsOp < 0) { // if there is no = operator this key/value pair are
	            // malformed so do our best and move onto next pair
	            continue;
	         }
	         String key = params[i].substring(0, indexOfEqualsOp);
	         String value = params[i].substring(indexOfEqualsOp + 1, params[i].length());
	         decodedParams.put(key, value);
	      }
	      return decodedParams;
   }
   
   /**
    * Utility method that takes and URL encoded UTF-8 string (type x-www-form-urlencoded) 
    * and decodes it. Encoded string will have lots of % signs in it, something like:
    * 
    * <tt>xsl=http%3A%2F%2Fduvel.ucd.ie%2F%7Esneely%2Fconstruct%2Fdefault.xsl</tt>
    * 
    * If the decoding fails this method will log the failure and return an empty string.
    * 
    * @param the_urlEncodedString the string to decode
    * @return the decoded string or am empty string if this fails
    */
   protected String decodeURLEncodedString(String the_urlEncodedString) {
	   String decodedString = new String();
	      try {
	    	  decodedString = URLDecoder.decode(the_urlEncodedString, "UTF-8");
	      } catch (UnsupportedEncodingException uee) {
	    	  getLogger().warning(
	    			  "Unsupported encoding trying to decode URL Encoded string request in HTTPPort "
	    			  + uee.getMessage());
		  }
	   return decodedString;
   }
   
   /**
    * Internal helper method that generates the HTTP header
    * 
    * @param the_httpCode the HTTP code
    * @param the_contentType the content type (html, xml etc.)
    * @param the_length the length of the entire response
    * @return the HTTP header string
    */
   protected String getHttpHeader(int the_httpCode, String the_contentType, int the_length) {
      String reasonPhrase;

      switch (the_httpCode) {
      case HTTP_OK:
         reasonPhrase = HTTP_OK_REASON_PHRASE;
         break;
      case HTTP_BAD_REQUEST:
         reasonPhrase = HTTP_BAD_REQUEST_REASON_PHRASE;
         break;
      case HTTP_FORBIDDEN:
         reasonPhrase = HTTP_FORBIDDEN_REASON_PHRASE;
         break;
      case HTTP_NOT_FOUND:
         reasonPhrase = HTTP_NOT_FOUND_REASON_PHRASE;
         break;
      case HTTP_BAD_METHOD:
         reasonPhrase = HTTP_BAD_METHOD_REASON_PHRASE;
         break;
      case HTTP_SERVER_ERROR:
         reasonPhrase = HTTP_SERVER_ERROR_REASON_PHRASE;
         break;
      default:
         reasonPhrase = "unknown http code";
      }
      return "HTTP/1.1 " + the_httpCode + " " + reasonPhrase + "\r\n"
      + "Server: " + SERVER_IDENTIFIER + "\r\n"
      + "Content-Length: " + the_length + "\r\n"
      + "Connection: close\r\n"
      + "Content-Type: " + the_contentType + "\r\n" + "\r\n";
   }

   /**
    * Returns the HTML code that defines a query to Construct on http://[hostname]:[port]/ with
    * param "q" for the query.
    * 
    * @return the HTML string for the web page
    */
   protected String getHtmlForQueryPage() {
      return "<html>\n"
            + "<head><title>Query Construct</title></head>\n\n"
            + "<body>\n\n"
            + getHtmlForms()
      		+ "</body>\n"
            + "</html>\n";
   		}

   /**
    * Returns the HTML code that defines a query to Construct on http://[hostname]:[port]/ with
    * param "q" for the query and an insert form http://[hostname]:[port]/ with
    * param "i".
    * 
    * @return the HTML string for the web page
    */
   protected String getHtmlForQueryPageAndMalformedQueryError() {
      return "<html>\n"
            + "<head><title>Query Construct</title></head>\n\n"
            + "<body>\n\n"
            + "<p><strong>Malformed query string in request. You need to pass a query as parameter"
            + "<tt>query</tt> or <tt>q</tt> from the HTML form as a GET request.</strong></p>\n"
            + getHtmlForms()
            + "</body>\n"
      		+ "</html>\n";
      }

   /**
    * Method that generates four HTML forms for sending SPARQL queries and data inserts to Construct via GET and POST
    * @return the HTML code for the forms and some instructional text for embedding in an HTML page
    */
   protected String getHtmlForms() {
       return "<p>Query Construct with SPARQL GET request via this form.</p>\n\n"
       + "Query:"
       + "<form method=\"GET\" action=\"http://" + my_hostname + ":" + my_port + "/\">\n"
       + "<textarea name=\"q\" cols=\"64\" rows=\"10\">"
       + "SELECT ?subject ?predicate ?object WHERE {?subject ?predicate ?object}" 
       + "</textarea><br/>"
       + "URL of XSLT to apply (optional):<br/>"
       + "<input type=\"text\" name=\"xsl\" size=\"56\" value=\"http://duvel.ucd.ie/~sneely/construct/default.xsl\"><br/>"
       + "<input type=\"submit\" value=\"Submit Query\">\n"
       + "</form>\n\n"
       + "<p><hr/></p>"
       + "<p>Insert data into Construct via GET with this form.</p>\n\n"
       + "Insert:"
       + "<form method=\"GET\" action=\"http://" + my_hostname + ":" + my_port + "/\">\n"
       + "<textarea name=\"i\" cols=\"64\" rows=\"10\">"
       + "<http://www.pervasive-ontologies.org/ontologies/sensors/bluetooth#reading00:19:63:96:56:01@00:80:98:94:AE:4B@1201631502><http://www.pervasive-ontologies.org/ontologies/sensors/bluetooth#spotted>\"00:19:63:96:56:01\"." 
       + "</textarea><br/>"
       + "Expiry time for data (optional):<br/>"
       + "<input type=\"text\" name=\"expiry\" size=\"15\" value=\"20000\"><br/>"
       + "<input type=\"submit\" value=\"Submit Data\">\n"
       + "</form>\n\n"
       + "<p><hr/><hr/></p>"
       + "<p>Query Construct with SPARQL via POST with this form.</p>\n\n"
       + "Query:"
       + "<form method=\"POST\" action=\"http://" + my_hostname + ":" + my_port + "/\">\n"
       + "<textarea name=\"q\" cols=\"64\" rows=\"10\">"
       + "SELECT ?subject ?predicate ?object WHERE {?subject ?predicate ?object}" 
       + "</textarea><br/>"
       + "URL of XSLT to apply (optional):<br/>"
       + "<input type=\"text\" name=\"xsl\" size=\"56\" value=\"http://duvel.ucd.ie/~sneely/construct/default.xsl\"><br/>"
       + "<input type=\"submit\" value=\"Submit Query\">\n"
       + "</form>\n\n"
       + "<p><hr/></p>"
       + "<p>Insert data into Construct via POST with this form.</p>\n\n"
       + "Insert:"
       + "<form method=\"POST\" action=\"http://" + my_hostname + ":" + my_port + "/\">\n"
       + "<textarea name=\"i\" cols=\"64\" rows=\"10\">"
       + "<http://www.pervasive-ontologies.org/ontologies/sensors/bluetooth#reading00:19:63:96:56:01@00:80:98:94:AE:4B@1201631502><http://www.pervasive-ontologies.org/ontologies/sensors/bluetooth#spotted>\"00:19:63:96:56:01\"." 
       + "</textarea><br/>"
       + "Expiry time for data (optional):<br/>"
       + "<input type=\"text\" name=\"expiry\" size=\"15\" value=\"20000\"><br/>"
       + "<input type=\"submit\" value=\"Submit Data\">\n"
       + "</form>\n\n";
   }
   
   /**
    * Constructs an RDF string from the results of a SPARQL query
    * 
    * @param a_resultString
    *           the string containing the results of a SPARQL query
    * @return the RDF string in XML format [ <resultSet><result><subject>value</subject><predicate>value</prediocate><object>value>object></result><result>...]
    *         created from the input string.
    */
   protected String createResultSetString(final String a_resultString) {

      ResultSet resultSet;
      StringBuffer rdfString = new StringBuffer("\n<resultSet>\n");
      // Create a result set
      final Model model = ModelFactory.createDefaultModel();
      final StringReader modelReader = new StringReader(a_resultString);
      model.read(modelReader, null, "N-TRIPLE");
      resultSet = ResultSetFactory.fromRDF(model);
      while (resultSet.hasNext()) {
         final QuerySolution solution = resultSet.nextSolution();
         rdfString.append("  <result>\n");
         for (Iterator it = solution.varNames(); it.hasNext();) {
            String nextVar = (String) it.next();
            final RDFNode rdfnode = solution.get(nextVar);
            rdfString.append("    <" + nextVar + ">");
            rdfString.append(rdfnode);
            rdfString.append("</" + nextVar + ">\n");
         }
         rdfString.append("  </result>\n");
      }
      rdfString.append("</resultSet>\n");
      return rdfString.toString();
   }

   /**
    * Constructs an RDF string from the results of a SPARQL query
    * 
    * @param a_resultString
    *           the string containing the results of a SPARQL query
    * @param a_stylesheet a stylesheet to embed in the XML
    * @return the RDF string in XML format created from the input string.
    */
   protected String createXMLFromResultSet(final ResultSet a_resultSet) {
      return ResultSetFormatter.asXMLString(a_resultSet);
   }

   /**
    * Constructs an RDF string from the results of a SPARQL query
    * 
    * @param a_resultString
    *           the string containing the results of a SPARQL query
    * @param a_stylesheet stylesheet to transform the XML
    * @return the RDF string in XML format created from the input string.
    */
   protected String createXMLFromResultSet(final ResultSet a_resultSet, String a_stylesheet) {
      return ResultSetFormatter.asXMLString(a_resultSet, a_stylesheet);
   }
   
   /**
    * Gets the org.construct_infrastructure.component.discovery.RegistryService and registers the http
    * port for discovery and use by the outside world.
    */
   public void onRun() {
      final String description = "Http port: Connect with HTTP to query Construct or insert data using "
            + "GET and POST requests. Send URL encoded data (as request URL of GET; message-body of POST) containing "
            + "the query or insert command. SPARQL queries should be labelled with query= or q=. Inserts "
            + "labelled with insert= or i= (in N-3 form). You can optionally add an expiry time for inserted data with expiry=. "
            + "The HttpPort response to a query will be an XML document. If you want to apply an XSL style sheet to this send xsl= "
            + "parameter along with the query. The HttpPort response to an insert will be an XML document describing the status of your request."
            + "The best way to play with the Http port is to start Construct and open http://localhost:8888/ in a browser.";
      final Object hostNameProperty = ConstructProperties.getHostName();
      if (hostNameProperty == null) {
         getLogger().info("Not registering with registry service - no hostname property");
      } else {
         final String host = (String) hostNameProperty;
         final int port = my_socket.getLocalPort();
         final String misc = "See example applications.";
         final ServiceComponentDescriptor httpportDescriptor = new ServiceComponentDescriptor(
               HP_NAME, description, host, port, misc);
         my_registryService.registerService(httpportDescriptor);
      }
   }

   /**
    * Cancel the cycle timer before shutting down.
    */
   public void onShutdown() {
      if (my_socket != null) {
         my_socket.shutdown();
      }
   }

   /**
    * Used by the http port to gain a reference to the data store and the registry service.
    * 
    * @throws NoSuchComponentException
    *            if an attempt is made to access a component which doesnt exist.
    */
   public void setupComponentLinks() throws NoSuchComponentException {
      my_dataStoreManager = (DataStoreManager) ComponentRegistry.getComponent(DSTORE_MANAGER);
      my_registryService = (RegistryService) ComponentRegistry.getComponent(RSERVICE_MANAGER);
   }

}
