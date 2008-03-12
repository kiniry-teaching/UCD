<?php
	include("include/header.php");
?>
<div id="bookprofile">
<?php
//TODO - Thomas - username() and isLoggedIn() needed here

$isbn = $_GET["isbn"]; //Gets the isbn from the address
include("include/book_functions.php");
fetchBookFromDB($isbn);

echo(
	"<p id='images'>
		<a href='" . $largeImg . "'><img src='" . $mediumImg . "' alt='Click to enlarge' /></a>
	</p>
	<p id='titleandauthor'>
		<h1>" . $title . "</h1>
		<h2>" . $titleLong . "</h2>
		<h3>by " . $authors . "</h3>
	</p>
	<p id='detailedinfo'>
		<b>ISBN:</b> " . $isbn . "<br/>
		<b>Publisher:</b> " . $publisher . "<br/>
		<b>No of Pages:</b> " . $noOfPages . "<br/>
		<b>Edition:</b> " . $binding . "<br/>
		<b>DDC:</b> " . $ddc . "<br/>
		<b>LCC:</b> " . $lcc
	. "</p>
	<p id='description'>
		<h4>Description</h4>" .
		$description
	. "</p>"
);

/*availability($isbn);
requestBook($isbn, $username);
noOfRequests($isbn);
getReviewed($isbn, $username);*/
?>
</div>
<?php
	include("include/footer.php");
?>