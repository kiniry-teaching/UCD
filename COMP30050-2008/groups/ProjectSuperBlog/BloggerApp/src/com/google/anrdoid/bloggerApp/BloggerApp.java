package com.google.anrdoid.bloggerApp;

import android.app.Activity;
import android.os.Bundle;

public class BloggerApp extends Activity {
    /** Called when the activity is first created. */
    @Override
    protected void onCreate(Bundle savedValues)
    {
       super.onCreate(savedValues);

       /* FOR TESTING PURPOSES: Load view from XML source.
        * Load the compiled layout resource into the window's
        * default ViewGroup 
        * */
       //setContentView(R.layout.main);
       
       //setContentView(R.layout.screen_1_main_menu);
       setContentView(R.layout.screen_2_atom_feeds);
      
       //restoreValues(savedValues);
    } 
}