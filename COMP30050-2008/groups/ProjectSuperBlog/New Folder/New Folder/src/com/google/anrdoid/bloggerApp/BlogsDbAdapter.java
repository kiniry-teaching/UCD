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

import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.List;

import android.content.ContentValues;
import android.content.Context;
import android.database.Cursor;
import android.database.sqlite.SQLiteDatabase;

/**
 * Simple notes database access helper class. Defines the basic CRUD operations
 * for the notepad example, and gives the ability to list all notes as well as
 * retrieve or modify a specific note.
 * 
 * This has been improved from the first version of this tutorial through the addition
 * of better error handling and also using returning a Cursor instead of using
 * a collection of inner classes (which is less scalable and not recommended).
 */
public class BlogsDbAdapter {

    public static final String TITLE="title";
    public static final String BODY="body";
    public static final String ROWID="id";
    public static final String BLOGID="blogID";
    
    private static final String DATABASE_NAME = "Blogs";
    private static final String DATABASE_TABLE = "post";
    private static final String DATABASE_VERIFY = "verify";
    private static final int DATABASE_VERSION = 2;
    
    
    
    private static final String DATABASE_CREATE =
        "create table " + DATABASE_TABLE + " ("
        	+ "id integer primary key,"
            + "title text not null,"
            + "blogID text not null,"
            + "body text not null);";

    private static final String VERIFY_CREATE = 
    		"create table " + DATABASE_VERIFY + " ("
    			+"confirm text not null);";
    
    private SQLiteDatabase Db;

    
    public BlogsDbAdapter(Context ctx) {

        try {
            Db = ctx.openDatabase(DATABASE_NAME, null);
        } catch (FileNotFoundException e) {
            try {
                Db =
                    ctx.createDatabase(DATABASE_NAME, DATABASE_VERSION, 0,
                        null);
                Db.execSQL(DATABASE_CREATE);
                Db.execSQL(VERIFY_CREATE);
            } catch (FileNotFoundException e1) {
                Db = null;
            }
        }
    }

    public void close() {
        Db.close();
    }

    /**
     * Create a new Blog using the title and body provided. If the Blog is successfully created
     * return the new rowId for that Blog, otherwise return a -1 to indicate failure.
     * @param title the title of the Blog
     * @param body the body of the Blog
     * @return rowId or -1 if failed
     */
    public long createBlog(BlogEntry blog) {
        ContentValues initialValues = new ContentValues();
        
        initialValues.put(ROWID, blog.id);
        initialValues.put(TITLE, blog.title);
     //   initialValues.put(BLOGID, blog.blogID);
        initialValues.put(BODY, blog.body);
       return  Db.insert(DATABASE_TABLE, null, initialValues);
    }

    /**
     * Delete the Blog with the given rowId
     * @param rowId id of Blog to delete
     * @return true if deleted, false otherwise
     */
    public boolean deleteBlog(long rowId) {
        return Db.delete(DATABASE_TABLE, "id" + "=" + rowId, null) > 0;
    }

    /**
     * Return a Cursor over the list of all Blogs in the database
     * @return Cursor over all Blogs
     */
    public Cursor fetchAllBlogs() {
        return Db.rawQuery(DATABASE_TABLE, new String[] {
                "id", "title", "body"});
    }

    /**
     * Return a Cursor positioned at the Blog that matches the given rowId
     * @param rowId id of Blog to retrieve
     * @return Cursor positioned to matching Blog, if found
     * @throws SQLException if Blog could not be found/retrieved
     */
 /*   public Cursor fetchBlog(long rowId) throws SQLException {
        Cursor result = mDb.query(true, DATABASE_TABLE, new String[] {
                KEY_ROWID, KEY_TITLE, KEY_BODY}, KEY_ROWID + "=" + rowId, null, null,
                null, null);
        if ((result.count() == 0) || !result.first()) {
            throw new SQLException("No Blog matching ID: " + rowId);
        }
        return result;
    }
*/
    /**
     * Update the Blog using the details provided. The Blog to be updated is specified using
     * the rowId, and it is altered to use the title and body values passed in
     * @param rowId id of Blog to update
     * @param title value to set Blog title to
     * @param body value to set Blog body to
     * @return true if the Blog was successfully updated, false otherwise
     */
  /*  public boolean updateBlog(long rowId, String title, String body) {
        ContentValues args = new ContentValues();
        args.put(KEY_TITLE, title);
        args.put(KEY_BODY, body);
        return mDb.update(DATABASE_TABLE, args, KEY_ROWID + "=" + rowId, null) > 0;
    }*/

    public List<BlogEntry> fetchAll()
    {
    	ArrayList<BlogEntry> ret = new ArrayList<BlogEntry>();
    	Cursor c = 
    		Db.query(DATABASE_TABLE, new String[] {
    				"id", "title", "body"}, null, null, null, null, null);
    	int numRows = c.count();
    	c.first();
    	for (int i = 0; i < numRows; ++i) {
    		BlogEntry row = new BlogEntry();
    		row.id = c.getLong(0);
    		row.title = c.getString(1);
    		row.body = c.getString(2);
    		
    		ret.add(row);
    		c.next();
    	}
    			return ret;
    		
    	}

    public BlogEntry fetchBlog(long Id)
    {
    	BlogEntry row = new BlogEntry();
    	
    	Cursor c = 
    		Db.query(DATABASE_TABLE, new String[] {
    				"id", "title", "body"},"id=" + Id, null, null, null, null);
    	if(c.count() > 0) {
    		c.first();

    		row.id = c.getLong(0);
    		
    		row.title = c.getString(1);
    		row.body = c.getString(2);
    		
    			return row;
    	}else {
    		row.id = -1;
    	}
    		return row;
    	}
    
    }



