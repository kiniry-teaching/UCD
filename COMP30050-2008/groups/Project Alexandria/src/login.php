
<?php
include("include/header.php"); //page header

include("include/loginfunctions.php"); //including all the methods that will be needed to login
?>
<form action="login.php" method="post">
Username: <input type="text" name="username" /><br />
Password: <input type="password" name="password" /><br />
<input type="radio" name="remember" value="true">Remember Me?<br />
<input type="submit" />
</form>
<?php
include("include/user_variables.php");

$EnteredUsername = $_POST[username];
$EnteredPassword = $_POST[password];
$remember = $_POST[remember];

login($EnteredUsername, $EnteredPassword, $remember);

include("include/footer.php"); //page footer
?>