<?php include("include/header.php"); //page header
	$username = $_SESSION['username'];

	include("connection.php"); //Connects to database
	mysql_query("DELETE FROM users_online WHERE username='$username'");
	
			unset($_SESSION['username']);
			unset($_SESSION['password']);	
			echo($username." has been logged out.<br />");		
include("include/footer.php"); //page footer
?>
