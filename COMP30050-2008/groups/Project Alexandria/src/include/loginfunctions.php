
<?php

function login($enteredUsername, $enteredPassword)

/*	Master method for Login
*	This method will call checkMatch, 
*	which will in turn call checkName() & checkPassword()
*/

//

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

{
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