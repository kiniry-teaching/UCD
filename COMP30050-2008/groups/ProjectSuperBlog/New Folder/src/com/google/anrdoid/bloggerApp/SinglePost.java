package com.google.anrdoid.bloggerApp;

import android.app.Activity;
import android.os.Bundle;
import android.view.View;
import android.widget.Button;
import android.widget.TextView;

//author: Peter Morgan

public class SinglePost extends Activity {

	private TextView mTitleText;
    private TextView mBodyText;
    private Long mRowId;
    private BlogsDbAdapter mDbHelper;
    private BlogEntry log;
    private String title;
    private String body;
    
    @Override
    protected void onCreate(Bundle icicle) {
    	super.onCreate(icicle);
        
        mDbHelper = new BlogsDbAdapter(this);
   //     mDbHelper.open();
       
        setContentView(R.layout.screen_4_single_post);
       
        mTitleText = (TextView) findViewById(R.id.s4_blog_post_title);
        mBodyText = (TextView) findViewById(R.id.s4_blog_post);
       
        Button back = (Button) findViewById(R.id.back);
       
        mRowId = icicle != null ? icicle.getLong(BlogsDbAdapter.ROWID) : null;
        if (mRowId == null) {
            Bundle extras = getIntent().getExtras();
            mRowId = extras != null ? extras.getLong(BlogsDbAdapter.ROWID) : null;
        }
       
        populateFields();
       
        back.setOnClickListener(new View.OnClickListener() {

            public void onClick(View view) {
                setResult(RESULT_OK);
                finish();
            }

        });
    }
    
    private void populateFields() {
    	if (mRowId != null) {
    		
    		log = mDbHelper.fetchBlog(mRowId);
    		title = log.title;
    		body = log.body;

            mTitleText.setText(title);
            mBodyText.setText(body);
    	}
    }
}

