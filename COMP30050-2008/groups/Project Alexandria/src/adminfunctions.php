
<?php
/* admin_user_functions
*
*
*/
include "userfunctions.php";
if(isAdmin=="true")//this loop is to prevent any non-admins from acessing the admin functions
{
	function updateUser(){	
	include("connection.php"); //Connects to database

	mysql_query("UPDATE users 
		SET e-mail = '$title',
		userlevel = '$userlevel',
	
		WHERE username = '$username'");

	mysql_close($con);
	}




//the line below will print an error if someone who is not an admin tries to access the admin functions(attempts to access an admin only page)
}else{	echo("You must be an admin to access this page");	} 

?>

