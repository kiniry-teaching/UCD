<?php
	include("include/header.php");
?>
<div id="bookprofile">
<?php
//TODO - Thomas - username() and isLoggedIn() needed here

$isbn = $_GET["isbn"];
include("include/book_functions.php");
fetchBookFromDB($isbn);

/*availability($isbn);
requestBook($isbn, $username);
noOfRequests($isbn);
getReviewed($isbn, $username);*/
?>
</div>
<?php
	include("include/footer.php");
?>