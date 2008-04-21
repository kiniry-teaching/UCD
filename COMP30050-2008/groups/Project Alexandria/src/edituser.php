<?php 
session_start(); 
/*starts the session that will be used on all pages from login to logout*/ 
?>
<div>
<?php
/*	Project Alexandria 2008	*/

	/****************************************************/
	/*	edituser.php									*/
	/*	the admin page for editing users information	*/
	/*	e.g userlevel									*/
	/****************************************************/
	
include("include/header.php"); 			//page header
include("include/adminfunctions.php");	//include the admin function necessary for editing user information
	$username = $_SESSION['username']; 	//Gets the username from the session

	if(isAdmin($username)==True)
	{
		include("include/global_user_variables.php");
			//TODO - obtain username of the profile to be edited
		?>
			
			
			
		<b>Edit User Profile</b>
		<div>
		<?php echo("<b>".$user."</b><br />");?>
		
		<form action="edituser.php" method="post">
		
		<b>Change Userlevel:</b><br />
		WARNING: Changing the userlevel will change a users access levels to the Library.<br /> 
		Username: <input type="text" name="user" /><br />
		<input type="radio" name="userlevel" value="user">General User (Default Setting)<br />
		<input type="radio" name="userlevel" value="librarian">Librarian<br />
		<input type="radio" name="userlevel" value="admin">Administrator<br />
		<input type="radio" name="userlevel" value="banned">Banned<br />
		<input type="hidden" name="state" value="1" /><input type="submit" />
		</form>
		</div>
		<?php
		
		if($_POST['state'] == 1)
		{
			$username = $_POST[user];	//username of the user being edited
			$userlevel = $_POST[userlevel];	//userlevel to be assigned to that user
			
			if($userlevel=="user")
			{$userlevel=1;}
			if($userlevel=="admin")
			{$userlevel=9;}
			if($userlevel=="librarian")
			{$userlevel=8;}
			if($userlevel=="banned")
			{$userlevel=0;} 
			
			editUserLevel($user, $userlevel);
		}
	}
else
	{	
	echo("You must be an admin to access this page");
	}	
	
include("include/footer.php"); //page footer
?>
</div>
