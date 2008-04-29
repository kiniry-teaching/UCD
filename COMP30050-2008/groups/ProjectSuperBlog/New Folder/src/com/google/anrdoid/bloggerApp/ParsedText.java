
package com.google.anrdoid.bloggerApp;

//author: Peter Morgan

public class ParsedText {
     private String extractedString = null;
     long test= 10;
     String[] body = new String[25];
     String[] title = new String[25];
     String[] author = new String[25];
     String[] update = new String[25];
     String[] published = new String[25];
     
     String[] tempTitle = new String[26];
     int counter = 0;
     int tempCount = 0;
     
     public String getExtractedString() {
          return extractedString;
     }
     
     public void setTitle(String extractedString) {
          this.title[counter] = extractedString;
          this.tempTitle[tempCount] = extractedString;
          tempCount++;
     }
     
     public void setBody(String extractedString) {
         this.body[counter] = extractedString;
    }
     
     public void setAuthor(String extractedString) {
         this.author[counter] = extractedString;
    }
     
     public void setUpdate(String extractedString) {
         this.update[counter] = extractedString;
    }
     
     public void setPublish(String extractedString) {
         this.published[counter] = extractedString;
    }
     
     public void popTable(BlogsDbAdapter blog)
     {
    	 BlogEntry posts = new BlogEntry();
    	 for(int i =0; i < counter; i++)
    	 {
   // 		 posts.blogID = tempTitle[0];
    		 posts.id = i;
    		 posts.title = title[i];
    		 posts.body = body[i];
    	//	 posts.published = published[i];
    	//	 posts.updated = update[i];
    	//	 posts.author = author[i];
    		 
    		 blog.createBlog(posts);
    	 }

     }
     
     public void counter(){
    	 counter++;
     }
     
     public String getTitle(){
    	 return tempTitle[0];
     }
}