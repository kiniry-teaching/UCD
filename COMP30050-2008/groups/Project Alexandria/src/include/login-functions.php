
<?php
/*	Project Alexandria 2008	*/

	/********************************************************/
	/*	login-functions.php									*/
	/*	all the functions necessary for loging a user in 	*/
	/*	and ensuring that all their details are correct		*/
	/********************************************************/
include "include/userfunctions.php";

function login($username, $password, $remember){
	/********************************************************************/
	/*	Login()															*/
	/*	if checkMatch() returns true, login continues 					*/
	/*	to login the user in so that they can use the library			*/
	/*	It does this by adding the user to the users_online database	*/
	/*	and by starting a session,										*/
	/*	if the users has selected remember me, a cookie is created		*/
	/*	if checkMatch() returns false, an error is thrown 				*/
	/********************************************************************/

	if(checkMatch($username, $password)==True)
	{
		$time=time();
		include("connection.php"); //Connects to database
		$sql="INSERT INTO users_online (username, timestamp)
		VALUES ('$username', '$time')";
				if (!mysql_query($sql,$con))
			{
				die('Error: ' . mysql_error());
			}
			else
			{
				/************************************************/
   				/*	this starts a session, allowing the user	*/
				/*	to perform functions on different pages		*/
				/*	without having to login each time,			*/
				/*	sessions are destroyed when the user logsout*/
 				/************************************************/
				$md5pass = md5($password);	 
				$_SESSION['username'] = $username;
				$_SESSION['password'] = $md5pass;
				
				if($remember=="true")
				{
					/************************************************/
					/*	this sets a cookie if the user has selected	*/
					/*	the "remember me" option on the login form	*/
					/*	the cookie will expire in 30 days unless 	*/
					/*	renewed										*/
					/************************************************/
					setcookie("cookname", $_SESSION['username'], time()+60*60*24*30, "/");
					setcookie("cookpass", $_SESSION['password'], time()+60*60*24*30, "/");
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
function checkMatch($username, $password){
	/****************************************************/
	/*	checkMatch()									*/
	/*	checks to see if checkName() & checkPassword() 	*/
	/*	have returned true, if they have checkMatch()   */
	/*	returns true									*/
	/****************************************************/
	
	
	
if (checkName($username)==True)
{
	
	 if(checkPassword($username, $password)==True)
		{
			if(isBanned($username)==True)
			{
			echo("<b>The user ".$username." is Banned!</b><br />");
			return False;
			}
			else
			{
			return True;
			}
		}
	else
		{
		return False;
		}
}
else
{
return False;
}
}/*checkMatch*/

function checkName($username){
	/****************************************************/
	/*	checkName()										*/
	/*	checks to see if the entered username exists on */
	/*	database & returns True if it does				*/
	/****************************************************/
	
include("connection.php"); //Connects to database
$result = mysql_query("SELECT * FROM users	
   WHERE username ='$username'");
   
   if($result=="0")
   {
   echo("<b>The username ".$username." does not exist.</b> <br />");
   return False;
   } 
   else
   {
   return True;
   }
}/*checkName*/


function checkPassword($username, $password){
	/****************************************************/
	/*	checkPassword()									*/
	/*	checks to see if the entered password matches 	*/
	/*	that which corresponds to the entered username	*/
	/****************************************************/
   include("connection.php"); //Connects to database
    	$result = mysql_query("SELECT * FROM users
		WHERE username='$username'");

	while($row = mysql_fetch_array($result)){
		$DBpassword=$row['password']; //retrives the password from the database
		} 
   
   /*	encrypts the password to allow comparison */
   /*	to the encrypted password in the database */
	$passwordHash = md5($password);

	if ($passwordHash != $DBpassword)
	{
		echo("<p>Incorrect Password.</p>");
		return False;
	}
	else
	{
		return True;
	}
   
  /* 
   if($DBpassword==$md5pass) //true if the password matches the username
	{
	return True;
	}
	else
	{
	echo("<p>Incorrect Password.</p>");
	return False;
	}
 */
}/*checkPassword*/

/*	login-functions	*/
?>
