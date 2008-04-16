
<?php
/*	Master method for Login
*	This method will call checkMatch, 
*	which will in turn call checkName() & checkPassword()
*/
function login($Username, $Password, $remember){

include("connection.php"); //Connects to database
$result = mysql_query("SELECT * FROM users	
   WHERE username ='$username'");
   
   if($result=="0")
   {
   echo("<b>The username ".$Username." does not exist.</b> <br /> <b>Please Try Again!<br />");
   } 
   else
   {
   include("connection.php"); //Connects to database
   $result2 = mysql_query("SELECT password FROM users	
   WHERE username ='$username'");
   if($result2==$password)
	{
		{include("connection.php"); //Connects to database
		$sql="INSERT INTO users_online (username, timestamp)
		VALUES ('$username', NOW())";
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

 	  		/*
   			*	sets a cookie if the user has selected the remember me option on the login form
 			*/
   			if($remember=="true"){
     	 	setcookie("cookname", $_SESSION['username'], time()+60*60*24*100, "/");
     	 	setcookie("cookpass", $_SESSION['password'], time()+60*60*24*100, "/");
  	 		}
		
			echo("Login Sucessful.<br />");	
			}
	}
	else
	{
   	echo("<b>That is not the correct password for ".$Username.".</b> <br /> <b>Please Try Again!<br />");
   	}	
}
function checkMatch($enteredUsername, $enteredPassword){
/*
*	compares the username and the password that were entered to see if they match those stored in the database
*/
}/*checkMatch*/

function checkName($enteredUsername){
/*
* 	checks to see if the entered name exsists in the database
*	if it exsists the checkPassword method is called
*/
}/*checkName*/

function checkPassword($username, $enteredUsername){
/*
*	checks to see if the entered password matches that which corresponds to the entered username
*/
}/*checkPassword*/



?>