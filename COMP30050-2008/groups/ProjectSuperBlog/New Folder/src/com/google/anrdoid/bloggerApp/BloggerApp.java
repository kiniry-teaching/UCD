package com.google.anrdoid.bloggerApp;

import android.app.Activity;
import android.content.Intent;
import android.os.Bundle;
import android.view.View;
import android.widget.Button;

public class BloggerApp extends Activity
{
   public void onCreate(Bundle icicle)
   {
      super.onCreate(icicle);
      setContentView(R.layout.screen_1_main_menu);
      Button a = (Button) findViewById(R.id.s1_feeds_button);
      a.setOnClickListener(new View.OnClickListener() {
         public void onClick(View arg0) {
         Intent i = new Intent(BloggerApp.this, Atom_Feeds.class);
         startActivity(i);
         }
      });
     
      Button b = (Button) findViewById(R.id.s1_blogger_button);
      b.setOnClickListener(new View.OnClickListener() {
         public void onClick(View arg0) {
         //Intent i = new Intent(BloggerApp.this, Atom_Feeds.class);
         //startActivity(i);
        	 setContentView(R.layout.screen_5_access_blogger);
         }
      });
   }
}
