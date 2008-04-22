package com.google.anrdoid.bloggerApp;

import android.app.ListActivity;
import android.content.Intent;
import android.database.Cursor;
import android.os.Bundle;
import android.view.View;
import android.widget.Button;
import android.widget.EditText;
import android.widget.SimpleCursorAdapter;
import android.widget.TextView;


public class SingleFeed extends ListActivity {

	private TextView mTitleText;
    private EditText mBodyText;
    private Long mRowId;
    private BlogsDbAdapter mDbHelper;
    private Cursor mPostsCursor;
    private static final int ACTIVITY_CREATE=0;
    private static final int ACTIVITY_EDIT=1;
    
    @Override
    protected void onCreate(Bundle icicle) {
    	super.onCreate(icicle);
        
        mDbHelper = new BlogsDbAdapter(this);
        mDbHelper.open();
       
        setContentView(R.layout.screen_3_single_feed);
       
        mTitleText = (TextView) findViewById(R.id.s3_feed_name);
 //       mBodyText = (EditText) findViewById(R.id.body);
       
        mRowId = icicle != null ? icicle.getLong(BlogsDbAdapter.KEY_ROWID) : null;
        if (mRowId == null) {
            Bundle extras = getIntent().getExtras();
            mRowId = extras != null ? extras.getLong(BlogsDbAdapter.KEY_ROWID) : null;
        }
       
        Button back = (Button) findViewById(R.id.s3_back);
        back.setOnClickListener(new View.OnClickListener() {
           public void onClick(View arg0) {
           Intent i = new Intent(SingleFeed.this, Atom_Feeds.class);
           startActivity(i);
           }
        });
        
        Button newpost = (Button) findViewById(R.id.s3_newpost);
        newpost.setOnClickListener(new View.OnClickListener() {
           public void onClick(View arg0) {
           Intent i = new Intent(SingleFeed.this, BlogEdit.class);
           startSubActivity(i, ACTIVITY_CREATE);
           }
        });
    }
    
    private void fillData() {
        // Get all of the rows from the database and create the item list
        Cursor BlogsCursor = mDbHelper.fetchAllBlogs();
        startManagingCursor(BlogsCursor);
        
        // Create an array to specify the fields we want to display in the list (only TITLE)
        String[] from = BlogsDbAdapter.getPosts(mRowId);
        
        // and an array of the fields we want to bind those fields to (in this case just text1)
        int[] to = new int[]{R.id.text2};
        
        // Now create a simple cursor adapter and set it to display
        SimpleCursorAdapter Blogs = 
        	    new SimpleCursorAdapter(this, R.layout.posts_row, BlogsCursor, from, to);
        setListAdapter(Blogs);
    } 
    
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
    }
}

