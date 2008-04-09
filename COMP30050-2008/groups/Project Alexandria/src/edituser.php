
<?php
include("include/header.php"); //page header
/*	edituser.php
 *	the admin page for editing users information
 *	e.g userlevel, etc
 */
//include("include/adminfunctions.php");
	//TODO - code
?>
	
<b>Edit User Profile</b>
<div>
<form action="edituser.php" method="post">
New Password:<input type="password" name="password1" /><br />
Re-Enter New Password:<input type="password" name="password2" /><br />
Enter your new e-mail:<input type="text" name="e-mail1" /><br />
Re-Enter new e-mail:<input type="text" name="e-mail2" /><br />
<input type="submit" />
</form>
</div>

<?php
$password1 = $_POST[password1];
$password = $_POST[password2];
$email1 = $_POST[e-mail1];
$email2 = $_POST[e-mail2];

if($password1!=$password2)
{echo("The passwords do not match, please try again.");}

else
{
//for testing only
echo($password1." - ".$password2);

}


//TODO - more code

include("include/footer.php"); //page footer
?>
