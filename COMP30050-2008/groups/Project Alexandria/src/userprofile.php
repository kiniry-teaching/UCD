<?php 
session_start(); 
/*starts the session that will be used on all pages from login to logout*/ 
?>
<div>
<?php

include("include/header.php"); //page header
/*
*	profile.php
*	This is the profile page of a user
*	This page can be viewed in 3 different ways
*	1. as viewed by any user
*	2. as viewed by any user viewing their own page
*	3. as viewed by an admin		
*/
include("include/userfunctions.php");

$username = $_SESSION['username']; //Gets the username from the session


	include("connection.php"); //Connects to the database
	$result = mysql_query("SELECT * FROM users
		WHERE username='$username'");

	while($row = mysql_fetch_array($result)){
		$userlevel=$row['userlevel'];
		$dateregistered=$row['timestamp'];
		echo("timestamp = ".$dateregistered."<br />");
		registered
		echo("timestamp = ".$dateregistered."<br />");
	}//gets the user information needed from the user database

?>
<div>
	<table width="500" align="center">
		<tr>
			<td width="20%">Username:</td>
			<td width="80%"><?php echo("<b>".$username."</b>");?></td>
		</tr>
		<tr>
			<td>Registered:</td>
			<td><?php echo($dateregistered);?></td>
		</tr>
		
		<tr>
			<td>Userlevel:</td>
			<td><?php
				if($userlevel==0){echo("Banned");}
				if($userlevel==1){echo("User");}
				if($userlevel==8){echo("Librarian");}
				if($userlevel==9){echo("Administrator");	}
				?></td>
		</tr>		
		
		
		
		<tr>
			<td>Books Reviewed:</td>
			<td><?php //TODO - getBooksReviewed ?></td>
		</tr>

	</table>
</div>

<?php
include("include/footer.php");
?>
</div>