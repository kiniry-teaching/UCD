package com.google.android.Superblog1;
import java.io.ByteArrayInputStream;
import java.io.UnsupportedEncodingException;
import java.net.URLEncoder;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import org.apache.http.util.ByteArrayBuffer;

import android.content.Context;
import android.net.http.EventHandler;
import android.net.http.Headers;
import android.net.http.RequestQueue;
import android.net.http.SslCertificate;
import android.util.Log;

public class HTTPpost {

     // ===========================================================
     // Fields
     // ===========================================================

     private Context context;
     private String url;
     private String variables;
     private Method method;
     
     public enum Method {
          POST,
          GET
     }

     // ===========================================================
     // 'Constructors'
     // ===========================================================

     // Constructor for requests without variables
     public HTTPpost(Context c, String url, Method method){
          this(c, url, method, null);
     }
     
     // Constructor for requests with variables
     public HTTPpost(Context c, String url, Method method, Map<String,String> variables) {
          this.context = c;
          this.url = url;
          this.variables = "";
          this.method = method;
          
          /* Prepare the variables we are going to send. */
          if(variables != null){
               try {
                    StringBuilder b = new StringBuilder();
                    Set keys = variables.keySet();
                    for(Iterator i = keys.iterator(); i.hasNext();){
                         String key = (String)i.next();
                         b.append(key);
                         b.append("=");
                         b.append(URLEncoder.encode(variables.get(key), "UTF-8"));
                         if(i.hasNext()){
                              b.append("&");
                         }
                    }
                    this.variables = b.toString();
               } catch (UnsupportedEncodingException e) {
                    Log.e("HTTPpost", "Unsupported Encoding Exception");
                    return;
               }
          }
     }

     private PostHandler handler;

     public void setHandler(PostHandler h){
          handler = h;
     }

     public void go(){
          /* Create a new EventHandler defined above, to handle what gets returned. */
          MyEventHandler myEvH = new MyEventHandler(handler);

          /* Create a new HTTP-RequestQueue. */
          android.net.http.RequestQueue rQueue = new RequestQueue(context);        

          /* Create a header-hashmap */
          Map<String, String> headers = new HashMap<String, String>();
          /* and put the Default-Encoding for html-forms to it. */
          headers.put("Content-Type", "application/x-www-form-urlencoded");

          if(method == Method.GET){
               // Perform the request with GET
               if(!variables.equals("")){
                    url = url + "?" + variables;
               }
               rQueue.queueRequest(url, "GET", headers, myEvH, null, 0, false);
          } else if(method == Method.POST){
               /* And put the encoded bytes into an BAIS,
                * where a function later can read bytes from. */
               byte[] POSTbytes = variables.getBytes();
               ByteArrayInputStream baos = new ByteArrayInputStream(POSTbytes);
               rQueue.queueRequest(url, "POST", headers, myEvH, baos, POSTbytes.length, false);               
          }
          //t
          /* Wait until the request is complete.*/
          rQueue.waitUntilComplete();
     }
     //ddsds

     // ===========================================================
     // Worker Class
     // ===========================================================

     private class MyEventHandler implements EventHandler {
          private PostHandler handler;

          /** Will hold the data returned by the URLCall. */
          ByteArrayBuffer baf = new ByteArrayBuffer(20);

          MyEventHandler(PostHandler callback) {
               this.handler = callback;
          }

          public void data(byte[] bytes, int len) {
               baf.append(bytes, 0, len);
          }

          public void endData() {
               handler.run(new String(baf.toByteArray()));
          }

          public void status(int arg0, int arg1, int arg2, String s) {
               // Status can be OK, Not Found, others...
               handler.status(s);
          }

          public void error(int i, String s) {
               handler.error(s);
          }

          public void handleSslErrorRequest(int arg0, String arg1, SslCertificate arg2) { }
          public void headers(Iterator arg0) { }
          public void headers(Headers arg0) { }
     }

     public static abstract class PostHandler {
          abstract void run(String response);
          void status(String status) {}
          void error(String error) {}
     }
}