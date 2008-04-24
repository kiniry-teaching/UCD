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

import android.content.ContentValues;
import android.content.Context;
import android.database.Cursor;
import android.database.SQLException;
import android.database.sqlite.SQLiteDatabase;

import java.io.FileNotFoundException;

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

    public static final String KEY_TITLE="title";
    public static final String KEY_BODY="body";
    public static final String KEY_ROWID="_id";
    public String[] posts = new String[10];
    public static String[] titles = new String[10]; 
    int counter;
    /**
     * Database creation sql statement
     */
    private static final String DATABASE_CREATE =
        "create table Blogs (_id integer primary key autoincrement, "
            + "title text not null, body text not null);";

    private static final String DATABASE_NAME = "data";
    private static final String DATABASE_TABLE = "blogs";
    private static final int DATABASE_VERSION = 2;

    private SQLiteDatabase mDb;
    private final Context mCtx;

    /**
     * Constructor - takes the context to allow the database to be opened/created
     * @param ctx the Context within which to work
     */
    public BlogsDbAdapter(Context ctx) {
        this.mCtx = ctx;
    }
    
    /**
     * Open the Blogs database. If it cannot be opened, try to create a new instance of
     * the database. If it cannot be created, throw an exception to signal the failure
     * @return this (self reference, allowing this to be chained in an initialization call)
     * @throws SQLException if the database could be neither opened or created
     */
    public BlogsDbAdapter open() throws SQLException {
        try {
            mDb = mCtx.openDatabase(DATABASE_NAME, null);
        } catch (FileNotFoundException e) {
            try {
                mDb =
                    mCtx.createDatabase(DATABASE_NAME, DATABASE_VERSION, 0,
                        null);
                mDb.execSQL(DATABASE_CREATE);
            } catch (FileNotFoundException e1) {
                throw new SQLException("Could not create database");
            }
        }
        return this;
    }

    public void close() {
        mDb.close();
    }

    /**
     * Create a new Blog using the title and body provided. If the Blog is successfully created
     * return the new rowId for that Blog, otherwise return a -1 to indicate failure.
     * @param title the title of the Blog
     * @param body the body of the Blog
     * @return rowId or -1 if failed
     */
    public long createBlog(String title, String body) {
        ContentValues initialValues = new ContentValues();
        initialValues.put(KEY_TITLE, title);
        initialValues.put(KEY_BODY, body);
        return mDb.insert(DATABASE_TABLE, null, initialValues);
    }

    /**
     * Delete the Blog with the given rowId
     * @param rowId id of Blog to delete
     * @return true if deleted, false otherwise
     */
    public boolean deleteBlog(long rowId) {
        return mDb.delete(DATABASE_TABLE, KEY_ROWID + "=" + rowId, null) > 0;
    }

    /**
     * Return a Cursor over the list of all Blogs in the database
     * @return Cursor over all Blogs
     */
    public Cursor fetchAllBlogs() {
        return mDb.query(DATABASE_TABLE, new String[] {
                KEY_ROWID, KEY_TITLE, KEY_BODY}, null, null, null, null, null);
    }

    /**
     * Return a Cursor positioned at the Blog that matches the given rowId
     * @param rowId id of Blog to retrieve
     * @return Cursor positioned to matching Blog, if found
     * @throws SQLException if Blog could not be found/retrieved
     */
    public Cursor fetchBlog(long rowId) throws SQLException {
        Cursor result = mDb.query(true, DATABASE_TABLE, new String[] {
                KEY_ROWID, KEY_TITLE, KEY_BODY}, KEY_ROWID + "=" + rowId, null, null,
                null, null);
        if ((result.count() == 0) || !result.first()) {
            throw new SQLException("No Blog matching ID: " + rowId);
        }
        return result;
    }

    /**
     * Update the Blog using the details provided. The Blog to be updated is specified using
     * the rowId, and it is altered to use the title and body values passed in
     * @param rowId id of Blog to update
     * @param title value to set Blog title to
     * @param body value to set Blog body to
     * @return true if the Blog was successfully updated, false otherwise
     */
    public boolean updateBlog(long rowId, String title, String body) {
        ContentValues args = new ContentValues();
        args.put(KEY_TITLE, title);
        args.put(KEY_BODY, body);
        return mDb.update(DATABASE_TABLE, args, KEY_ROWID + "=" + rowId, null) > 0;
    }
    
    public void updateFeeds(String text)
    {
    		posts[counter] = text;
    		counter++;
    }
    
    public static String[] getPosts(long rowId)
    {
    	return titles;
    }
    
}

