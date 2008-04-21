<?php 
session_start(); 
/*starts the session that will be used on all pages from login to logout*/ 
?>
<div>
<?php
 
/*	Project Alexandria 2008	*/

	/************************************************************/
	/*	login.php												*/
	/*	the login page allowing the user to access the library	*/
	/*	Most actions of this page are covered 					*/
	/*	in the included login-functions.php						*/
	/************************************************************/


include("include/header.php"); ?>
<form action="login.php" method="post">
Username: <input type="text" name="username" /><br />
Password: <input type="password" name="password" /><br />
<input type="radio" name="remember" value="true">Remember Me?<br />
<input type="hidden" name="state" value="1" /><input type="submit" />
</form>
<?php

if($_POST['state'] == 1){

	include("include/user_variables.php");
	include("include/login-functions.php"); //including all the functions that will be needed to login
	$username = $_POST[username];
	$password = $_POST[password];
	$remember = $_POST[remember];
	
	if(strlen($username) == 0)
	{
	echo("<p>Username field is empty, please enter a username.</p>");
	}
	else
		if(strlen($password) == 0)
		{
		echo("<p>Password field is empty, please enter a password.</p>");
		}
		else
		{
				login($username, $password, $remember);
		}
}

include("include/footer.php"); //page footer
/*	login.php	*/
?>
</div>