
<?php
include("include/header.php"); //page header
include("include/userfunctions.php");
/*	editprofile.php
 *	the user page for editing their own information information
 *	e.g. password, e-mail
 */
 ?>
 
<table align="center" width="600">
	<td>
		<tr>

echo("<b>Edit Your Profile</b>");
		</tr>
	</td>
	
	<td>
		<tr>
	<?php
echo("<b>Change Your Password</b>");
<form action="editprofile.php" method="post">
Enter new e-mail: <input type="text" name="e-mail1" />
Re-Enter new e-mail: <input type="text" name="e-mail2" />
enter your password <input type="password" name="password" />
<input type="submit" />
</form>
?>
		</tr>
	</td>
</table>
<?php

 //TODO - lots more coding


include("include/footer.php"); //page footer
?>

