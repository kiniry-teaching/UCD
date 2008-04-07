
<?php
include("include/header.php"); //page header
/*	edituser.php
 *	the admin page for editing users information
 *	e.g userlevel, etc
 */
include("include/adminfunctions.php");
	//TODO - code
	?>
<div>
<?php
echo("<b>Edit User Profile</b>");
<form action="editprofile.php" method="post">
Username: <input type="text" name="username" />
New Username: <input type="text" name="newUsername" />
Enter your e-mail: <input type="text" name="e-mail1" />
Re-Enter e-mail: <input type="text" name="e-mail2" />
<input type="submit" />
</form>
?>
</div>
<?php
//TODO - more code

include("include/footer.php"); //page footer
?>
