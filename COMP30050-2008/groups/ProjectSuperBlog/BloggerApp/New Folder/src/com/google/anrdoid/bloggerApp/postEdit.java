/*
 * Copyright (C) 2008 Google Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.google.anrdoid.bloggerApp;

import android.app.Activity;
import android.database.Cursor;
import android.os.Bundle;
import android.view.View;
import android.widget.Button;
import android.widget.EditText;

public class postEdit extends Activity {

	private EditText mTitleText;
    private EditText mBodyText;
    private Long mRowId;
    private BlogsDbAdapter mDbHelper;
    
    @Override
    protected void onCreate(Bundle icicle) {
    	super.onCreate(icicle);
        
        mDbHelper = new BlogsDbAdapter(this);
        mDbHelper.open();
       
        setContentView(R.layout.feed_edit);
       
        mTitleText = (EditText) findViewById(R.id.title);
        mBodyText = (EditText) findViewById(R.id.body);
       
        Button confirmButton = (Button) findViewById(R.id.confirm);
       
        mRowId = icicle != null ? icicle.getLong(BlogsDbAdapter.KEY_ROWID) : null;
        if (mRowId == null) {
            Bundle extras = getIntent().getExtras();
            mRowId = extras != null ? extras.getLong(BlogsDbAdapter.KEY_ROWID) : null;
        }
       
        populateFields();
       
        confirmButton.setOnClickListener(new View.OnClickListener() {

            public void onClick(View view) {
            	//mDbHelper.updateFeeds(mTitleText);
                finish();
            }
           
        });
    }
    
    private void populateFields() {
    	if (mRowId != null) {
            Cursor Blog = mDbHelper.fetchBlog(mRowId);
            startManagingCursor(Blog);
            mTitleText.setText(Blog.getString(
    	            Blog.getColumnIndex(BlogsDbAdapter.KEY_TITLE)));
            mBodyText.setText(Blog.getString(
                    Blog.getColumnIndex(BlogsDbAdapter.KEY_BODY)));
    	}
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
        populateFields();
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

