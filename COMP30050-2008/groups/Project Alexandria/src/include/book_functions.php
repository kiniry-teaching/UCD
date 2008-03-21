<?php
include_once('include/variables.php');

/****************************************************************
* 																*
* fetchBookFromDB(isbn) - 										*
* Produces all data for that ISBN from the books database. It	*
* does this through while loop with a sql query of SELECT and	*
* WHERE, the where being where the ISBN matches.				*
* Data being transmitted:										*
* An ISBN is sent and the full details of the book are returned	*
* (these include the ISBN, title, long title, author,			*
* description, DDC No., etc.).									*
* 																*
****************************************************************/

function fetchBookFromDB($isbn){
	include('include/variables_global.php');
	//Necessary for editing the variables above (see the PHP manual for more details)
	
	include("connection.php"); //Connects to the database
	
	$result = mysql_query("SELECT * FROM books
		WHERE isbn='$isbn'");

	while($row = mysql_fetch_array($result)){
		$isbn=$row['isbn'];
		$title=$row['title'];
		$titleLong=$row['titleLong'];
		$authors=$row['authors'];
		$publisher=$row['publisher'];
		$noOfPages=$row['noOfPages'];
		$binding=$row['binding'];
		$ddc=$row['ddc'];
		$lcc=$row['lcc'];
		$description=$row['description'];
		$largeImg=$row['largeImg'];
		$mediumImg=$row['mediumImg'];
		$smallImg=$row['smallImg'];
		$noOfCopies=$row['noOfCopies'];
	}
}

/****************************************************************
* 																*
* availability(isbn) - 											*
* Requests the number of copies of a book (using the sql query	*
* WHERE to find the row with the matching ISBN) from books. It	*
* then does the same with the books_onloan but this time uses	*
* COUNT to get the number of instances of the ISBN and then		*
* compares the numbers, where the numbers are equal it prints	*
* On Loan else Available.										*
* Data being transmitted:										*
* Sends the same ISBN to the books and books_onloan				*
* databases and retrieves the number of copies from the former	*
* and from the latter the number of times the ISBN appears.		*
* 																*
****************************************************************/

function availability($isbn){
	$noOfCopies = "";
	
	include("connection.php"); //Connects to the database
	$result = mysql_query("SELECT * FROM books
		WHERE isbn='$isbn'");

	while($row = mysql_fetch_array($result)){
		$noOfCopies=$row['noOfCopies'];
	}
	
	$result = mysql_query("SELECT *
		FROM books_onloan
			WHERE isbn='$isbn'");
	$noOfCopies_onLoan = mysql_num_rows($result);
	
	if($noOfCopies == $noOfCopies_onLoan){
		echo "On Loan";
	}
	else{
		echo "Available";
	}

}

/****************************************************************
* 																*
* requestBook(isbn, username) - 								*
* Adds the pair isbn and username to the books_requested		*
* database by use of the sql query INSERT.						*
* Data being transmitted:										*
* Sends the ISBN and username to the database books_requested.	*
* 																*
****************************************************************/
/*
function requestBook($isbn, $username){
	//TODO - Ryan - See comment
}*/

/****************************************************************
* 																*
* noOfRequests(isbn)											*
* Uses the sql query COUNT to return the number of rows where	*
* isbn occurs as the ISBN.										*
* Data being transmitted:										*
* The ISBN is being sent and the number of instances is being	*
* returned.														*
* 																*
****************************************************************/

function noOfRequests($isbn){
	include("connection.php"); //Connects to the database
	$result = mysql_query("SELECT *
		FROM books_requests
			WHERE isbn = '$isbn'
	");
	$number = mysql_num_rows($result);
	echo $number;
}
/****************************************************************
* 																*
* getReviewed(isbn, username)									*
* Can be used to return all data from the books_reviewed		*
* database where the isbn and username match by use of a while	*
* loop and the sql query WHERE.									*
* Data being transmitted:										*
* Sends the ISBN and username and retrieves the full data where	*
* those match from the rows of books_reviewed.					*
* 																*
****************************************************************/

function getReviewed($isbn, $username){
	include("connection.php"); //Connects to the database
	$result = mysql_query("SELECT *
		FROM books_review
			WHERE isbn='$isbn' AND username='$username'");

	while($row = mysql_fetch_array($result)){
		echo "<div class='reviewrow'>";
			echo "<div class='reviewer'>" . $row['username'] . "</div>";
			echo "<div class='rating'>" . $row['rating'] . "</div>";
			echo "<div class='review'>" . $row['review'] . "</div>";
			echo "<p><a href=''>Add a review</a></p>";
		echo "</div>";
	}

}

/****************************************************************
* 																*
* tableOfBooks(searchterm, category)							*
* This uses a sql query inside a while loop to retrieve and		*
* print out a table containing all key details on books where	*
* the “category” (column) equals the “search term”. The table	*
* produced will have hyperlinked headers and the title of the	*
* books will be hyperlinked to that books profile page by use of*
* its ISBN.														*
* Data being transmitted:										*
* The “search term” and “category” are sent and the relevant	*
* details (by default the title, long title, author and genre)	*
* are returned.													*
* 																*
****************************************************************/

function tableOfBooks($searchterm, $category, $order){
	echo "<div id='search_table'>";
	
		echo "<div class='search_row_header'>";
			echo "<div class='search_image_header'>Image</div>";
			echo "<div class='search_title_header'><a href='search.php?searchterm=" . $searchterm . "&category=" . $category . "&order=title&state=2'>Title</a></div>";
			echo "<div class='search_titleLong_header'><a href='search.php?searchterm=" . $searchterm . "&category=" . $category . "&order=titleLong&state=2'>Title (Long)</a></div>";
			echo "<div class='search_authors_header'><a href='search.php?searchterm=" . $searchterm . "&category=" . $category . "&order=authors&state=2'>Authors</a></div>";
			echo "<div class='search_publisher_header'><a href='search.php?searchterm=" . $searchterm . "&category=" . $category . "&order=publisher&state=2'>Publisher</a></div>";
			echo "<div class='search_noOfPages_header'><a href='search.php?searchterm=" . $searchterm . "&category=" . $category . "&order=noOfPages&state=2'>No. of Pages</a></div>";
			echo "<div class='search_binding_header'><a href='search.php?searchterm=" . $searchterm . "&category=" . $category . "&order=binding&state=2'>Binding</a></div>";
		echo "</div>";
	include('connection.php');
	$result = mysql_query("SELECT * FROM books
	WHERE $category LIKE '%$searchterm%'
		ORDER BY $order");
	
	while($row = mysql_fetch_array($result)){
		echo "<div class='search_row'>";
			echo "<div class='search_image'><a href='" . $row['largeImg'] . "'><img src='" . $row['smallImg'] . "' alt='CLick to enlarge' /></a></div>";
			echo "<div class='search_title'><a href='bookprofile.php?isbn=" . $row['isbn'] . "'>" . $row['title'] . "</a></div>";
			echo "<div class='search_titleLong'>" . $row['titleLong'] . "</div>";
			echo "<div class='search_authors'><a href='search.php?searchterm=" . $row['authors'] . "&category=authors&state=1'>" . $row['authors'] . "</a></div>";
			echo "<div class='search_publisher'>" . $row['publisher'] . "</div>";
			echo "<div class='search_noOfPages'>" . $row['noOfPages'] . "</div>";
			echo "<div class='search_binding'>" . $row['binding'] . "</div>";
		echo "</div>";
	}
	
	echo "</div><!--End of search_table-->";
}
?>