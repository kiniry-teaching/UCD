
<div>
<?php
include("include/header.php");
include("userfunctions.php");

$result = mysql_query("SELECT * FROM users_friends
		WHERE username='$username'");
?>
<table align="center" width="500">
<tr>
	<td>
	Username:
	</td>
</tr>	
<?php
echo("".$username."");
?>

</table>
<?php
include("include/footer.php");
?>
</div>