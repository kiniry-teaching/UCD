
<?php
include("include/header.php"); //page header
/*	edituser.php
 *	the admin page for editing users information
 *	e.g userlevel, etc
 */
include("include/adminfunctions.php");
	//TODO - code
	?>

<?php
echo("<b>Edit User Profile</b>");?>
<div>
<form action="editprofile.php" method="post"><br/>
Username: <input type="text" name="username" /><br/>
New Username: <input type="text" name="newUsername" /><br/>
Enter your e-mail: <input type="text" name="e-mail1" /><br/>
Re-Enter e-mail: <input type="text" name="e-mail2" /><br/>
<input type="submit" />
</form>
</div>
<?php
//TODO - more code

include("include/footer.php"); //page footer
?>
