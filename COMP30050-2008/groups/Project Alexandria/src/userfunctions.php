
<?php
/*	userfunctions.php
*	these functions (isAdmin & isBanned) are used to return the users access privileges(or lack thereof)
*
*/



function isAdmin($username){
include("connection.php"); //Connects to database
	$result = mysql_query("SELECT userlevel FROM users
		WHERE username='$username'");
if($result==9)	//An admin has a userlevel of 9
{return true;}
else
{return false;}
}

function isBanned($username){
include("connection.php"); //Connects to database
	$result = mysql_query("SELECT userlevel FROM users
		WHERE username='$username'");
if($result==0)	//A banned user has a userlevel of 0
{return true;}
else
{return false;}
}

//incomplete
function isLoggedIn($username){
include("connection.php"); //Connects to database
	$result = mysql_query("SELECT * FROM users_online
		WHERE username='$username'");
if($result==9)	//An admin has a userlevel of 9
if()

}

?>
