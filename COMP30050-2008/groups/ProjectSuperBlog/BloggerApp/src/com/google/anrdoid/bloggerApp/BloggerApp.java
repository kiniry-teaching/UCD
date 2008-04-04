package com.google.anrdoid.bloggerApp;

import android.app.Activity;
import android.os.Bundle;

public class BloggerApp extends Activity {
    /** Called when the activity is first created. */
    @Override
    protected void onCreate(Bundle savedValues)
    {
       super.onCreate(savedValues);

       // Load the compiled layout resource into the window's
       // default ViewGroup
        setContentView(R.layout.main);
      
       //restoreValues(savedValues);
    } 
}