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
	}
}

/****************************************************************
* 																*
* availability(isbn) - 											*
* Requests the number of copies of a book (using the sql query	*
* WHERE to find the row with the matching ISBN) from &#65533;books&#65533;. It*
* then does the same with the &#65533;books_online&#65533; but this time uses	*
* COUNT to get the number of instances of the ISBN and then		*
* compares the numbers, where the numbers are equal it prints	*
* &#65533;On Loan&#65533; else &#65533;Available&#65533;.									*
* Data being transmitted:										*
* Sends the same ISBN to the &#65533;books&#65533; and &#65533;books_onloan&#65533;			*
* databases and retrieves the number of copies from the former	*
* and from the latter the number of times the ISBN appears.		*
* 																*
****************************************************************/
/*
availability($isbn){
	//TODO - Ryan - See comment
}*/

/****************************************************************
* 																*
* requestBook(isbn, username) - 								*
* Adds the pair &#65533;isbn&#65533; and &#65533;username&#65533; to the &#65533;books_requested&#65533;	*
* database by use of the sql query INSERT.						*
* Data being transmitted:										*
* Sends the ISBN and username to the database &#65533;books_requested&#65533;.*
* 																*
****************************************************************/
/*
requestBook($isbn, $username){
	//TODO - Ryan - See comment
}*/

/****************************************************************
* 																*
* noOfRequests(isbn)											*
* Uses the sql query COUNT to return the number of rows where	*
* &#65533;isbn&#65533; occurs as the ISBN.									*
* Data being transmitted:										*
* The ISBN is being sent and the number of instances is being	*
* returned.														*
* 																*
****************************************************************/
/*
noOfRequests($isbn){
	//TODO - Ryan - See comment
}*/

/****************************************************************
* 																*
* getReviewed(isbn, username)									*
* Can be used to return all data from the &#65533;books_reviewed&#65533;		*
* database where the isbn and username match by use of a while	*
* loop and the sql query WHERE.									*
* Data being transmitted:										*
* Sends the ISBN and username and retrieves the full data where	*
* those match from the rows of &#65533;books_reviewed&#65533;.				*
* 																*
****************************************************************/
/*
getReviewed($isbn, $username){
	//TODO - Ryan - See comment
}*/

?>