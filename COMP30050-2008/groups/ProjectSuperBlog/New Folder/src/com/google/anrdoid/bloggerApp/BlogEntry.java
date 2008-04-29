package com.google.anrdoid.bloggerApp;

//author: Peter Morgan

public class BlogEntry extends Object {
    public String title;
    public long id;
    public String blogID;
    public String body;
 //   public String published;
 //   public String updated;
 //   public String author;
    
    public BlogEntry(){
    	
    }
    
    public BlogEntry(long Id){
    	id = Id;
    }
}
