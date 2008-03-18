<?php
	include("include/header.php");
?>
<div id="bookprofile">
<?php
//TODO - Thomas - username() and isLoggedIn() needed here

$isbn = $_GET["isbn"]; //Gets the isbn from the address
include("include/book_functions.php");
fetchBookFromDB($isbn);

if($mediumImg != NULL){
	echo(
		"<p id='images'>
			<a href='" . $largeImg . "'><img src='" . $mediumImg . "' alt='Click to enlarge' /></a>
		</p>"
	);
}
echo(
	"<p id='titleandauthor'>
		<h1>" . $title . "</h1>
		<h2>" . $titleLong . "</h2>
		<h3>by " . $authors . "</h3>
	</p>
	<p id='detailedinfo'>
		<b>ISBN:</b> " . $isbn . "<br/>"
);

$detailsArray = array($publisher, $noOfPages, $binding, $ddc, $lcc);

for($k=0; $k<count($detailsArray); $k++){
	if($detailsArray[$k] != NULL){
		switch ($j){
			case 0: echo("<b>Publisher:</b> " . $publisher . "<br/>"); break;
			case 1: echo("<b>No of Pages:</b> " . $noOfPages . "<br/>"); break;
			case 2: echo("<b>Edition:</b> " . $binding . "<br/>"); break;
			case 3: echo("<b>DDC:</b> " . $ddc . "<br/>"); break;
			case 4: echo("<b>LCC:</b> " . $lcc); break;
		}
	}
}
	echo("</p>");
if($description != NULL){
	echo("<p id='description'><h4>Description</h4>" . $description . "</p>");
}

/*availability($isbn);
requestBook($isbn, $username);
noOfRequests($isbn);
getReviewed($isbn, $username);*/
?>
</div>
<?php
	include("include/footer.php");
?>