<?php
/**/	
/*	Login()
/*	This method will call checkMatch, 
/*	which will in turn call checkName() & checkPassword()
/********************************************************/
function login($username, $Password, $remember){

	if(checkMatch($username, $Password)==True)
	{
		$time=time();
		include("connection.php"); //Connects to database
		$sql="INSERT INTO users_online (username, timestamp)
		VALUES ('$username', '$time')";
				if (!mysql_query($sql,$con))
			{
				die('Error: ' . mysql_error());
			}
			else{
			/* 
	 		*	Username and password correct, register session variables
	 		*	$password is encrypted using the md5 hash function
	 		*/
			$md5pass = md5($password);	 
			$_SESSION['username'] = $username;
			$_SESSION['password'] = $md5pass;
			
			// Amal edited this part
			
			$_SESSION['user_id'] = $user_id;


 	  		/*
   			*	sets a cookie if the user has selected the remember me option on the login form
 			*/
   			if($remember=="true")
			{
     	 		setcookie("cookname", $_SESSION['username'], time()+60*60*24*100, "/");
     	 		setcookie("cookpass", $_SESSION['password'], time()+60*60*24*100, "/");
  	 		}
		
			echo($username." Logged in Sucessfully.<br />");	
			}
	}
	else
	{
   	echo(	
		"<b>Login Failed</b> <br />
		Please Try Again!<br />"
		);
   	}	
}
function checkMatch($username, $Password){
/*
*	compares the username and the password that were entered to see if they match those stored in the database
*/
if (checkName($username)==True&&checkPassword($username, $password)==True)
	{
	return True;
	}
else
	{
	return Fales;
	}

}/*checkMatch*/

function checkName($username){
/*
* 	checks to see if the entered name exsists in the database
*	if it exsists the checkPassword method is called
*/

include("connection.php"); //Connects to database
$result = mysql_query("SELECT * FROM users	
   WHERE username ='$username'");
   
   if($result=="0")
   {
   echo("<b>The username ".$username." does not exist.</b> <br /> <b>Please Try Again!<br />");
   return False;
   } 
   else
   {
   return True;
   }
}/*checkName*/

function checkPassword($username, $password){
/*
*	checks to see if the entered password matches that which corresponds to the entered username
*/
   include("connection.php"); //Connects to database
   $result2 = mysql_query("SELECT password FROM users	
   WHERE username ='$username'");
   if($result==$password) //true if the password matches the username
	{
	return True;
	}
	else
	{
	echo("<p>Incorrect Password, Please Try Again.</p>");
	return False;
	}

}/*checkPassword*/



?>