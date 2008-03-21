<?php
	include("include/header.php");
?>
<div id="adminbookmonitor">
<?php include('include/adminbook_functions.php');?>
<h1>Book Monitor</h1>
<h2>Books on-loan</h2>
<?php
if($_GET['state'] != NULL){
	switch ($_GET['state']){
		case 0: returned($_GET['isbn'], $_GET['username']); break;
		case 1: neverReturned($_GET['isbn'], $_GET['username']); break;
		case 2: renewed($_GET['isbn'], $_GET['username'], $_GET['date']); break;
		case 3: loaned($_GET['isbn'], $_GET['username'], $_GET['date']); break;
		case 4: neverloaned($_GET['isbn'], $_GET['username']); break;
	}
}

include('connection.php');
$result = mysql_query("SELECT * FROM books_onloan
	ORDER BY date");

echo "<div class='onloan_table'>";
	echo "<div class='onloan_row_header'>";
		echo "<div class='onloan_isbn_header'>ISBN</div>";
		echo "<div class='onloan_username_header'>Username</div>";
		echo "<div class='onloan_date_header'>Date</div>";
		echo "<div class='onloan_returned_header'>Returned</div>";
		echo "<div class='onloan_lost_header'>Lost</div>";
		echo "<div class='onloan_renew_header'>Renew</div>";
	echo "</div>";
while($row = mysql_fetch_array($result)){
	echo "<div class='onloan_row'>";
		echo "<div class='onloan_isbn'>" . $row['isbn'] . "</div>";
		echo "<div class='onloan_username'>" . $row['username'] . "</div>";
		echo "<div class='onloan_date'>" . date("d/m/y", $row['date']) . "</div>";
		echo "<div class='onloan_returned'><a href='adminbookmonitor.php?state=0&isbn=" . $row['isbn'] ."&username=" . $row['username'] . "'>Returned</a></div>";
		echo "<div class='onloan_lost'><a href='adminbookmonitor.php?state=1&isbn=" . $row['isbn'] ."&username=" . $row['username'] . "'>Lost</a></div>";
		echo "<div class='onloan_renew'><a href='adminbookmonitor.php?state=2&isbn=" . $row['isbn'] ."&username=" . $row['username'] . "&date=" . time() . "'>Renew</a></div>";
	echo "</div>";
}
echo "</div>";

?>
<h2>Pending book requests</h2>
<?php
include('connection.php');
$result = mysql_query("SELECT * FROM books_requests
	ORDER BY no");

echo "<div class='requests_table'>";
	echo "<div class='requests_row_header'>";
		echo "<div class='requests_isbn_header'>ISBN</div>";
		echo "<div class='requests_username_header'>Username</div>";
		echo "<div class='requests_loaned_header'>Loaded</div>";
		echo "<div class='requests_delete_header'>Delete</div>";
	echo "</div>";
while($row = mysql_fetch_array($result)){
	echo "<div class='requests_row'>";
		echo "<div class='requests_isbn'>" . $row['isbn'] . "</div>";
		echo "<div class='requests_username'>" . $row['username'] . "</div>";
		echo "<div class='requests_loaned'><a href='adminbookmonitor.php?state=3&isbn=" . $row['isbn'] ."&username=" . $row['username'] . "&date=" . time() . "'>Loaned</a></div>";
		echo "<div class='requests_delete'><a href='adminbookmonitor.php?state=4&isbn=" . $row['isbn'] ."&username=" . $row['username'] . "'>Delete</a></div>";
	echo "</div>";
}
echo "</div>";
?>

</div>
<?php
	include("include/footer.php");
?>