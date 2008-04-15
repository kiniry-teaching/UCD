
<?php
include("include/header.php"); //page header
/*	edituser.php
 *	the admin page for editing users information
 *	e.g userlevel, etc
 */
include("include/adminfunctions.php");
include("include/global_user_variables.php");
/*the above inclusion is to ensure that only admins may access this page*/
	//TODO - code
?>
	
<b>Edit User Profile</b>
<div>
<?php echo("<b>".$username."</b><br />");?>
<form action="edituser.php" method="post">
<b>Change Username:</b><br />
New Username:			<input type="text" name="username1" /><br />
Re-Enter New Username:	<input type="text" name="username2" /><br />
<input type="submit" />
</form>
<?php
$username1 = $_POST[username1];
$username2 = $_POST[username2];

if($username1==$username2)
{$username3=$username1}
else
{echo("The usernames do not match, please try again.");}
//for testing only
echo($password1." - ".$password2);

}
?>
<form action="edituser.php" method="post">
<b>Change Userlevel:</b><br />
WARNING: Changing the userlevel will change a users access levels to the Library.<br /> 
<input type="radio" name="userlevel" value="user">General User (Default Setting)<br />
<input type="radio" name="userlevel" value="librarian">Librarian<br />
<input type="radio" name="userlevel" value="admin">Administrator<br />
<input type="radio" name="userlevel" value="banned">Banned<br />
<input type="submit" />
</form>
</div>
<?php
$userlevel = $_POST[userlevel];

if($userlevel=="user")
{$userlevel=1;}
if($userlevel=="admin")
{$userlevel=9;}
if($userlevel=="librarian")
{$userlevel=8;}
if($userlevel=="banned")
{$userlevel=0;} 

function editUserLevel($username, $userlevel){

	{include("connection.php"); //Connects to database
	$sql="INSERT INTO users (userlevel,)
	VALUES ('$userlevel') WHERE username=$username";
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

}
include("include/footer.php"); //page footer
?>
