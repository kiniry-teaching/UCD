
<?php
include("include/header.php"); //page header
include("include/userfunctions.php");
/*	editprofile.php
 *	the user page for editing their own information information
 *	e.g. password, e-mail
 */
 ?>

<div>
<b>Edit Your Profile:</b><br />
 <?php echo("<b>".$username."</b><br />");?>
<form action="editprofile.php" method="post">
<b>Change Your e-mail:</b><br />
Enter new e-mail: <input type="text" name="e-mail1" /><br />
Re-Enter new e-mail: <input type="text" name="e-mail2" /><br />
<input type="submit" />
</form>
<?php
$email1 = $_POST[e-mail1];
$email2 = $_POST[e-mail2];

if($email1!=$email2)
{$email3=$email1;}
else
{echo("The emails do not match, please try again.");}
?>
</div>

<div>


<form action="editprofile.php" method="post">
<b>Change Your Password:</b><br />
Enter new password: <input type="password" name="password1" /><br />
Re-Enter new password: <input type="password" name="password2" /><br />
<input type="submit" />
</form>
</div>
<?php
$password1 = $_POST[password1];
$password = $_POST[password2];

if($password1==$password2)
{$password3=$password1;}
else
{echo("The passwords do not match, please try again.");}

echo($password3);
 //TODO - lots more coding

include("include/footer.php"); //page footer
?>

