
<div>
<?php
include("include/header.php");
include("connection.php");
include("include/userfunctions.php");

$result = mysql_query("SELECT * FROM users_friends
		WHERE username='$username'");
?>
<div align="center">
	Username:
	
<?php
echo("".$username."");
?>
</div>
<?php
include("include/footer.php");
?>
</div>