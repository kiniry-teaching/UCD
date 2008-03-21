<?php
	include("include/header.php");
?>
<div id="bookprofile">
<?php
//TODO - Thomas - username() and isLoggedIn() needed here

include("include/book_functions.php");
$isbn = $_GET["isbn"]; //Gets the isbn from the address
fetchBookFromDB($isbn);

if($mediumImg != NULL){
	echo(
		"<p id='images'>
			<a href='" . $largeImg . "'><img src='" . $mediumImg . "' alt='Click to enlarge' /></a>
		</p>"
	);
}
echo(
	"<div id='titleandauthor'>
		<h1>" . $title . "</h1>
		<h2>" . $titleLong . "</h2>
		<h3>by " . $authors . "</h3>
	</div>
	<p id='detailedinfo'>
		<b>ISBN:</b> " . $isbn . "<br/>"
);

$detailsArray = array($publisher, $noOfPages, $binding, $ddc, $lcc, $noOfCopies);

for($k=0; $k<count($detailsArray); $k++){
	if($detailsArray[$k] != NULL && $detailsArray[$k] != '0'){
		switch ($k){
			case 0: echo("<b>Publisher:</b> " . $publisher . "<br/>"); break;
			case 1: echo("<b>No of Pages:</b> " . $noOfPages . "<br/>"); break;
			case 2: echo("<b>Edition:</b> " . $binding . "<br/>"); break;
			case 3: echo("<b>DDC:</b> " . $ddc . "<br/>"); break;
			case 4: echo("<b>LCC:</b> " . $lcc . "<br/>"); break;
			case 5: echo("<b>Number of Copies:</b> " . $noOfCopies); break;
		}
	}
}
	echo("</p>");
if($description != NULL){
	echo("<p id='description'><h4>Description</h4>" . $description . "</p>");
}

echo "<p><b>Availability:</b> ";
	availability($isbn);
echo "</p>";
//requestBook($isbn, $username);
echo "<p><b>Number of requests:</b> ";
	noOfRequests($isbn);
echo "</p>";
echo "<p><b>User Reviews</b><br/>";
	getReviewed($isbn, '*');
echo "</p>";
?>
</div>
<?php
	include("include/footer.php");
?>