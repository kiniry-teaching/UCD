
<?php
include("include/header.php"); //page header

?>
<div>
<form action="register.php" method="post">
Enter a Username: <input type="text" name="username" /><br />
(Maximum Username Length 30 Chararcters)<br />
Enter your e-mail: <input type="text" name="email1" /><br />
Re-Enter e-mail: <input type="text" name="email2" /><br />
Enter a password: <input type="password" name="password1" /><br />
(Max Password Length 32 Chararcters)<br />
Re-Enter your password: <input type="password" name="password2" /><br />

<input type="hidden" name="state" value="1" /><input type="submit" />
</form>
</div>
<?php
include("include/user_variables.php");

if($_POST['state'] == 1){		
	$username = $_POST[username];
	$email1 = $_POST[email1];
	$email2 = $_POST[email2];
	$password1 = $_POST[password1];
	$password2 = $_POST[password2];
	
	include("include/registerfunctions.php");
	createUser($username, $password1, $userlevel, $email1, $email2, $password1, $password2);
}
include("include/footer.php"); //page footer
?>
