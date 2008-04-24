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

package com.google.android.BloggerApp;

import android.app.ListActivity;
import android.content.Intent;
import android.database.Cursor;
import android.os.Bundle;
import android.view.Menu;
import android.view.View;
import android.view.Menu.Item;
import android.widget.Button;
import android.widget.ListView;
import android.widget.SimpleCursorAdapter;

public class Atom_Feeds extends ListActivity {
    private static final int ACTIVITY_CREATE=0;
    private static final int ACTIVITY_EDIT=1;
    
    private static final int INSERT_ID = Menu.FIRST;
    private static final int DELETE_ID = Menu.FIRST + 1;

    private BlogsDbAdapter mDbHelper;
    
    /** Called when the activity is first created. */
    @Override
    public void onCreate(Bundle icicle) {
        super.onCreate(icicle);
        setContentView(R.layout.screen_2_atom_feeds);
        mDbHelper = new BlogsDbAdapter(this);
        mDbHelper.open();
        fillData();
        
        Button a = (Button) findViewById(R.id.button1);
        a.setOnClickListener(new View.OnClickListener() {
           public void onClick(View arg0) {
           Intent i = new Intent(Atom_Feeds.this, BloggerApp.class);
           startSubActivity(i, ACTIVITY_CREATE);
           }
        });
    }
    
    private void fillData() {
        // Get all of the rows from the database and create the item list
        Cursor BlogsCursor = mDbHelper.fetchAllBlogs();
        startManagingCursor(BlogsCursor);
        
        // Create an array to specify the fields we want to display in the list (only TITLE)
        String[] from = new String[]{BlogsDbAdapter.KEY_TITLE};
        
        // and an array of the fields we want to bind those fields to (in this case just text1)
        int[] to = new int[]{R.id.text1};
        
        // Now create a simple cursor adapter and set it to display
        SimpleCursorAdapter Blogs = 
        	    new SimpleCursorAdapter(this, R.layout.blogs_row, BlogsCursor, from, to);
        setListAdapter(Blogs);
    }
    
    @Override
    public boolean onCreateOptionsMenu(Menu menu) {
        super.onCreateOptionsMenu(menu);
        menu.add(0, INSERT_ID, R.string.menu_insert);
        menu.add(0, DELETE_ID, R.string.menu_delete);
        return true;
    }

    @Override
    public boolean onMenuItemSelected(int featureId, Item item) {
        switch(item.getId()) {
        case INSERT_ID:
            createBlog();
            return true;
        case DELETE_ID:
            mDbHelper.deleteBlog(getListView().getSelectedItemId());
            fillData();
            return true;
        }
       
        return super.onMenuItemSelected(featureId, item);
    }

    private void createBlog() {
        Intent i = new Intent(this, BlogEdit.class);
        startSubActivity(i, ACTIVITY_CREATE);
    }
    
    @Override
    protected void onListItemClick(ListView l, View v, int position, long id) {
        super.onListItemClick(l, v, position, id);
        Intent i = new Intent(this, SingleFeed.class);
        i.putExtra(BlogsDbAdapter.KEY_ROWID, id);
        startSubActivity(i, ACTIVITY_EDIT);
    }

    @Override
    protected void onActivityResult(int requestCode, int resultCode, String data, Bundle extras) {
        super.onActivityResult(requestCode, resultCode, data, extras);
        fillData();
    }
    
    
}

