<?php include("include/header.php");?>
<div>

<?php
//
//include("connection.php");
//include("include/userfunctions.php");
	$username = $_SESSION['username'];
	//echo($username);


$result = mysql_query("SELECT * FROM users_friends
					WHERE username='$username'");
			
?>
<div align="center">
	Username:
<?php
echo("   ".$username."<br />");
?>
	also Username:
<?php
echo("   ".$username."<br />");
?>

</div>
<?php
include("include/footer.php");
?>
</div>


