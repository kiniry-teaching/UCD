
<?php

include("loginMethods.php"); //including all the methods that will be needed to login

<form action="login.php" method="post">
Username: <input type="text" name="username" />
Password: <input type="password" name="password" />
<input type="submit" />
</form>

$EnteredUsername = $_POST[username];
$EnteredPassword = $_POST[password];

login($EnteredUsername, $EnteredPassword);

?>