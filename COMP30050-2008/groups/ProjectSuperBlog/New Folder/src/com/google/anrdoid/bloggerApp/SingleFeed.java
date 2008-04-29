package com.google.anrdoid.bloggerApp;

import java.net.URL;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;

import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.xml.sax.InputSource;
import org.xml.sax.XMLReader;

import android.app.ListActivity;
import android.content.Intent;
import android.os.Bundle;
import android.util.Log;
import android.view.View;
import android.widget.ArrayAdapter;
import android.widget.Button;
import android.widget.ListView;
import android.widget.TextView;


public class SingleFeed extends ListActivity {

    private final String MY_DEBUG_TAG = "WeatherForcaster";

	
    /** Connect over UCD proxy */
    Properties properties = System.getProperties();
    private BlogsDbAdapter mDbHelper;
    private List<BlogEntry> rows;
	private TextView mTitleText;
	String title;
    String titles;
    String next; 
    String testUR = null;
    URL testURL;
    @Override
    public void onCreate(Bundle icicle) {
         super.onCreate(icicle);

         setContentView(R.layout.screen_3_single_feed);
         mDbHelper = new BlogsDbAdapter(this);

         mTitleText = (TextView) findViewById(R.id.s3_feed_name);

         if (testUR == null) {
             Bundle extras = getIntent().getExtras();
             testUR = extras != null ? extras.getString(Atom_Feeds.test) : null;
         }
         
         try {
              /* Create a URL we want to load some xml-data from. */
       	     System.setProperty("https.proxyHost", "proxy.ucd.ie");
       	     System.setProperty("https.proxyPort", "8484");

              URL url = new URL(Atom_Feeds.test);

              /* Get a SAXParser from the SAXPArserFactory. */
              SAXParserFactory spf = SAXParserFactory.newInstance();
              SAXParser sp = spf.newSAXParser();

              /* Get the XMLReader of the SAXParser we created. */
              XMLReader xr = sp.getXMLReader();
              
              /* Create a new ContentHandler and apply it to the XML-Reader*/
              //ExampleHandler myExampleHandler = new ExampleHandler();
              //xr.setContentHandler(myExampleHandler);
              xmlParser max = new xmlParser();
              xr.setContentHandler(max);
              
              /* Parse the xml-data from our URL. */
              xr.parse(new InputSource(url.openStream()));
              /* Parsing has finished. */

              /* Our ExampleHandler now provides the parsed data to us. */
              ParsedText parsedTest =
                  max.getParsedData();
              
              for(int i = 0; i <100; i++)
              {
           	   mDbHelper.deleteBlog(i);
              }
              
              parsedTest.popTable(mDbHelper);
              title = parsedTest.getTitle();
              mTitleText.setText(title);
              
              // populate list
              fillData();
              

         } catch (Exception e) {
              Log.e(MY_DEBUG_TAG, "WeatherQueryError", e);
         }

  
        Button back = (Button) findViewById(R.id.s3_back);
        back.setOnClickListener(new View.OnClickListener() {
           public void onClick(View arg0) {
           Intent i = new Intent(SingleFeed.this, Atom_Feeds.class);
           startActivity(i);
           }
        });
    }
    
    private void fillData() {

 		List<String> items = new ArrayList<String>();
		rows = mDbHelper.fetchAll();

		for (BlogEntry row : rows) 
		{
			titles = row.title;		
			items.add(titles);
		}
		
 		ArrayAdapter<String> entries = 
		    new ArrayAdapter<String>(this, R.layout.blogs_row, items);
 		
		setListAdapter(entries);

    } 
    
    @Override
    protected void onListItemClick(ListView l, View v, int position, long id) {
        super.onListItemClick(l, v, position, id);
  //      log = mDbHelper.fetchBlog(id);
    //    Long abc= log.id;
        
    //    next = abc.toString();
        Intent i = new Intent(this, SinglePost.class);
        i.putExtra(BlogsDbAdapter.ROWID, id);
        startActivity(i);
    }
    
    /*
    @Override
    protected void onFreeze(Bundle outState) {
        super.onFreeze(outState);
        outState.putLong(BlogsDbAdapter.KEY_ROWID, mRowId);
    }
    
    @Override
    protected void onPause() {
        super.onPause();
        saveState();
    }
    
    @Override
    protected void onResume() {
        super.onResume();
    }
    
    private void saveState() {
        String title = mTitleText.getText().toString();
        String body = mBodyText.getText().toString();

        if (mRowId == null) {
            long id = mDbHelper.createBlog(title, body);
            if (id > 0) {
                mRowId = id;
            }
        } else {
            mDbHelper.updateBlog(mRowId, title, body);
        }
    }*/
}

