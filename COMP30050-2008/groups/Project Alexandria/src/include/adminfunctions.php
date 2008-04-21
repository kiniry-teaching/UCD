
<?php
/* 	admin_user_functions
*	All the functions needed to admin the user system
*	
*/
include "include/userfunctions.php";
if(isAdmin==True)//this loop is to prevent any non-admins from acessing the admin functions
{
	function updateUser($username, $email, $userlevel)	
		{
		/*function allow the admin to change certain details of a members account*/	
		include("connection.php"); //Connects to database
	
		mysql_query("UPDATE users 
			SET userlevel = '$userlevel',
			WHERE username = '$username'");
	
		mysql_close($con);
		}


	function editUserLevel($username, $userlevel)
	{
	/****************************************/
	/* editUserLevel() 						*/
	/*  changes the userlevel of any user	*/
	/****************************************/
	
		include("connection.php"); //Connects to database
		mysql_query("UPDATE users SET userlevel = '$userlevel',
		WHERE username = '$username'");
		
		/*
			$sql="INSERT INTO users (userlevel,)
			VALUES ('$userlevel') WHERE username=$username";
		*/
					if (!mysql_query($sql,$con))
				{
					die('Error: ' . mysql_error());
				}
		if($userlevel==0)
		{echo($username." has been made a General User!");}
		if($userlevel==9)
		{echo($username." has been made an Administrator!");}
		if($userlevel==8)
		{echo($username." has been made a Librarian!");}
		if(userlevel==0)
		{echo($username." has been banned!");}				
	}


//the line below will print an error if someone who is not an admin tries to access the admin functions(attempts to access an admin only page)
}else{	echo("You must be an admin to access this page");	} 

?>

