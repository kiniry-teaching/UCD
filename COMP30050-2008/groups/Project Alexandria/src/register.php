
<?php
include("include/header.php"); //page header

?>
<div>
<?php
<form action="register.php" method="post">
Enter a Username: <input type="text" name="username" />
Enter your e-mail: <input type="text" name="e-mail1" />
Re-Enter e-mail: <input type="text" name="e-mail2" />
Enter a password: <input type="password" name="password1" />
Re-Enter your password: <input type="password" name="password2" />

<input type="submit" />
</form>
?>
</div>
<?php
$username = $_POST[username];
$email1 = $_POST[email1];
$email2 = $_POST[email2];
$password1 = $_POST[password1];
$password2 = $_POST[password2];

//the following checks if the entered username already exsists in the database
$result = mysql_query("SELECT * FROM users	
   WHERE username ='$username'");
$ANOTHER_VARIABLE = mysql_num_rows($result);
if($ANOTHER_VARIABLE != 0)
	{echo "<p>". $username ."already exists, please try another username</p>";}
else if($email1 != $email2) //compares the two entered email addresses
	{echo "e-mail addresses do not match, please try again";}
else if($password1 != $password2) //compares the two entered passwords
	{echo "passwords do not match, please try again";}
else{
	if($username==$ADMIN_NAME)
	{$userlevl=='9';}else{$userlevel="1";}
		/*	sets the userlevel to 1(standard user) 
		*	if the username given matches the given name for the admin then that user is given the admin userlevel
		*	as the admin will be the first registered user they should register under the given name to gain admin functions
		*/
	
	function createUser($username, $password1, $userlevel, $e-mail1)
		/* 	createUser
		*	creates a new entry in the users database using the given details
		*/
	{include("connection.php"); //Connects to database
	$sql="INSERT INTO users (username, password, userlevel, e-mail, timestamp)
	VALUES ('$username','$password1','$userlevel','$e-mail1', NOW())";
				if (!mysql_query($sql,$con))
			{
				die('Error: ' . mysql_error());
			}
	echo "Account registered for ".$username."!";		
	}
}

include("include/footer.php"); //page footer
?>
