
<?php
/* admin_user_functions
*
*
*/
include "userfunctions.php";
if(isAdmin=="true")//this loop is to prevent any non-admins from acessing the admin functions
{
	function updateUser($username, $e-mail, $userlevel)	{
	/*function allow the admin to change certain details of a members account*/	
	include("connection.php"); //Connects to database

	mysql_query("UPDATE users 
		SET e-mail = '$e-mail',
		userlevel = '$userlevel',
	
		WHERE username = '$username'");

	mysql_close($con);
	}

if(isAdmin=="true")//this loop is to prevent any non-admins from acessing the admin functions
{
	function banUser($username){
	/*this function allows an admin to ban a user*/
	include("connection.php"); //Connects to database

	mysql_query("UPDATE users 
		userlevel = '0',
	
		WHERE username = '$username'");

	mysql_close($con);
	}


//the line below will print an error if someone who is not an admin tries to access the admin functions(attempts to access an admin only page)
}else{	echo("You must be an admin to access this page");	} 

?>

