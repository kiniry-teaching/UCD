
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
include("connection.php");
include("include/userfunctions.php");

$username=mysql_query("SELECT * FROM users	
   WHERE username ='$username'");
$dateregistered=mysql_query("SELECT timestamp FROM users	
   WHERE username ='$username'");
//TODO - add more variables
?>
<div>
	<table width="500" align="center">
		<tr>
			<td width="20%">Username:</td>
			<td width="80%"><?php echo("<b>".$username."</b>");?></td>
		</tr>
		<tr>
			<td>Date Registered:</td>
			<td><?php echo($dateregistered);?></td>
		</tr>
		<tr>
			<td></td>
			<td> </td>
		</tr>
	</table>
</div>

<?php
include("include/footer.php");
?>
</div>