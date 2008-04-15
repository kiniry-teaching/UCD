
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

$username = $_GET["username"]; //Gets the username from the address
getUserInfo($username);

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
			<td><?php //TODO - getBooksReviewed ?></td>
			<td> </td>
		</tr>
		<tr>
			<td><?php //TODO - getBooksReturned ?></td>
			<td> </td>
		</tr>
	</table>
</div>

<?php
include("include/footer.php");
?>
</div>