package com.google.anrdoid.bloggerApp;

import java.util.ArrayList;
import java.util.List;

import android.app.ListActivity;
import android.content.Intent;
import android.os.Bundle;
import android.view.View;
import android.widget.ArrayAdapter;
import android.widget.Button;
import android.widget.EditText;
import android.widget.ListView;

public class Atom_Feeds extends ListActivity {

    private BlogsDbAdapter mDbHelper;
    private List<BlogEntry> rows;
	private EditText add;
	private String url;
	public static String test;
	
	String http = "http://";
	String userIP = "192.168.1.106/";
	String end = ".xml";
	
    /** Called when the activity is first created. */
    @Override
    public void onCreate(Bundle icicle) {
        super.onCreate(icicle);
        setContentView(R.layout.screen_2_atom_feeds);
        mDbHelper = new BlogsDbAdapter(this);
        fillData();
        

        Button back = (Button) findViewById(R.id.s2_back);
        back.setOnClickListener(new View.OnClickListener() {
           public void onClick(View arg0) {
           Intent i = new Intent(Atom_Feeds.this, BloggerApp.class);
           startActivity(i);
           }
        });
        
        Button uri = (Button) findViewById(R.id.add);
        uri.setOnClickListener(new View.OnClickListener() {
           public void onClick(View arg0) {
        	   add = (EditText) findViewById(R.id.feed_uri);

        	   test = http + userIP + add.getText().toString() + end;
        	   
           Intent i = new Intent(Atom_Feeds.this, SingleFeed.class);
           i.putExtra(url, true);
           startActivity(i);
           }
        });
    }
    
    	  
        private void fillData() {
/*
     		List<String> items = new ArrayList<String>();
    		rows = mDbHelper.fetchAll();

    		for (BlogEntry row : rows) 
    		{
    			String test = row.blogID;		
    			items.add(test);
    		}
    		
     		ArrayAdapter<String> entries = 
    		    new ArrayAdapter<String>(this, R.layout.blogs_row, items);
     		
    		setListAdapter(entries);
*/
        	
       //default Feed
     		List<String> items = new ArrayList<String>();
     		test = http + userIP + "superblog1.xml";
     		items.add(test);
     		ArrayAdapter<String> entries = 
    		    new ArrayAdapter<String>(this, R.layout.blogs_row, items);
     		
    		setListAdapter(entries);
        } 

    @Override
    protected void onListItemClick(ListView l, View v, int position, long id) {
        super.onListItemClick(l, v, position, id);
        Intent i = new Intent(this, SingleFeed.class);
        i.putExtra(test, true);
        startActivity(i);
    }

    @Override
    protected void onActivityResult(int requestCode, int resultCode, String data, Bundle extras) {
        super.onActivityResult(requestCode, resultCode, data, extras);
        fillData();
    }
    
    public String getUR()
    {
    	return test;
    }
    
    
}

