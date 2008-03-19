<?php

//TODO - Thomas - isAdmin() needed here
include_once('include/variables.php');

$bookData = array($isbn,$title,$titleLong,$authors,$publisher,$noOfPages,$binding,$ddc,$lcc,$description,$largeImg,$mediumImg,$smallImg);

include("config.php"); //Holds the access keys for the API's
/****************************************************************
* 																*
* fetchBooks($isbn) - Takes the isbn and uses the available		*
* api's to find details on the book. It does this by going		*
* through a list of api accessers and when one returns not null	*
* it takes the details available and returns them by parsing	*
* the xml.														*
* Data being transmitted:										*
* The ISBN is sent and details of the book are sent back in xml	*
* form to be parsed.											*
* 																*
****************************************************************/

function fetchBooks($isbn){
	$dir="/include/include_adminbook_functions";
	$TrackDir=opendir("." . $dir);
	while ($file = readdir($TrackDir)) {  
		if ($file == "." || $file == ".."){}
		else if(substr($file,-3) == "php"){
			$toBeIncluded ='"' . $dir . '/' . $file . '"';
			include("$toBeIncluded");
		}
	}  
	closedir($TrackDir);
	
	fetchBooksAmazon($isbn, 0);
//TODO - Ryan - Fix isbndb timeout
//	fetchBooksISBNdb($isbn);
}

/****************************************************************
* 																*
* parseBookData() - Parses the array with book data so it is	*
* usable on other pages.										*
* 																*
****************************************************************/

function parseBookData(){
	include('include/variables_global.php');
	for($j=0; $j<count($bookData); $j++){
		switch ($j){
			case 0: $isbn = $bookData[$j]; break;
			case 1: $title = $bookData[$j]; break;
			case 2: $titleLong = $bookData[$j]; break;
			case 3: $authors = $bookData[$j]; break;
			case 4: $publisher = $bookData[$j]; break;
			case 5: $noOfPages = $bookData[$j]; break;
			case 6: $binding = $bookData[$j]; break;
			case 7: $ddc = $bookData[$j]; break;
			case 8: $lcc = $bookData[$j]; break;
			case 9: $description = $bookData[$j]; break;
			case 10: $largeImg = $bookData[$j]; break;
			case 11: $mediumImg = $bookData[$j]; break;
			case 12: $smallImg = $bookData[$j]; break;
		}
	}
}

/****************************************************************
* 																*
* function addBook($bookData) - Adds books to the &#65533;books&#65533;		*
* database. It does this by inputting the arguments in the		*
* database by use of the sql query INSERT.						*
* Data being transmitted:										*
* Data (the arguments) is sent into the &#65533;books&#65533; database.		*
* 																*
****************************************************************/

function addBook($isbn,$title,$titleLong,$authors,$publisher,$noOfPages,$binding,$ddc,$lcc,$description,$largeImg,$mediumImg,$smallImg,$noOfCopies){
	$imgarray = array($largeImg,$mediumImg,$smallImg);

	for($i=0; $i<count($imgarray); $i++){
		if($imgarray[$i] != NULL){
			$startpos = strrpos($imgarray[$i],"/I/") + 3;
			$filename = substr($imgarray[$i],$startpos);
			$uploaddir = "images/bookimages/" . $filename;
			
			if (file_exists($uploaddir)){
				echo "<p>" . $filename . " already exists</p>";
			}
			else{
				copy($imgarray[$i],$uploaddir);
				switch ($i){
					case 0: $largeImg = $uploaddir; break;
					case 1: $mediumImg = $uploaddir; break;
					case 2: $smallImg = $uploaddir; break;
				}
			}
		}
	}

	include("connection.php"); //Connects to database

	$result = mysql_query("SELECT * FROM books
		WHERE isbn='$isbn'");
	while($row = mysql_fetch_array($result)){
		$test = $row['isbn'];
	}
	
	if($test == NULL && $isbn != NULL){
		if($noOfCopies > 0){
			$sql="INSERT INTO books (isbn,title,titleLong,authors,publisher,noOfPages,binding,ddc,lcc,description,largeImg,mediumImg,smallImg,noOfCopies)
				VALUES ('$isbn','$title','$titleLong','$authors','$publisher','$noOfPages','$binding','$ddc','$lcc','$description','$largeImg','$mediumImg','$smallImg','$noOfCopies')";
			if (!mysql_query($sql,$con))
			{
				die('Error: ' . mysql_error());
			}
			echo "<p>1 record added</p>";
		}
		else{
			echo "<p>Number of copies must be greater than 0</p>";
		}
	}
	else if($test != NULL && $isbn != NULL){
		echo "<p><b>ISBN:</b> " . $isbn . " already exists</p>";
	}
	else if($isbn == NULL){
		echo "<p>ISBN is required</p>";
	}
	
	mysql_close($con);
}

/****************************************************************
* 																*
* updateBook() - 												*
* Uses the sql query UPDATE to replace the current stored data	*
* with what is passed as arguments where the ISBN matches.		*
* Data being transmitted:										*
* New data is sent to the books database to overwrite the		*
* existing entry for that book.									*
* 																*
****************************************************************/

function updateBook(){
	include('include/variables_global.php');
	
	include("connection.php"); //Connects to database

	mysql_query("UPDATE books
		SET title = '$title', titleLong = '$titleLong', authors = '$authors', publisher = '$publisher', noOfPages = '$noOfPages', binding = '$binding', ddc = '$ddc', lcc = '$lcc', description = '$description', largeImg = '$largeImg', mediumImg = '$mediumImg', smallImg = '$smallImg', noOfCopies = '$noOfCopies'
			WHERE isbn = '$isbn'");

	mysql_close($con);
}

/****************************************************************
* 																*
* adminTableOfBooks(searchterm, category)						*
* Produces a table of books dependant on criteria and links to	*
* delete and edit them using their ISBN.						*
* See also tableOfBooks().										*
* 																*
****************************************************************/
function adminTableOfBooks($searchterm, $category, $order){
	echo "<div id='search_table'>";
	
		echo "<div class='search_row_header'>";
			echo "<div class='search_isbn_header'>ISBN</div>";
			echo "<div class='search_title_header'>Title</div>";
			echo "<div class='search_titleLong_header'>Title (Long)</div>";
			echo "<div class='search_authors_header'>Authors</div>";
			echo "<div class='search_publisher_header'>Publisher</div>";
			echo "<div class='search_noOfPages_header'>No. of Pages</div>";
			echo "<div class='search_binding_header'>Binding</div>";
			echo "<div class='search_ddc_header'>DDC</div>";
			echo "<div class='search_lcc_header'>LCC</div>";
			echo "<div class='search_description_header'>Description</div>";
			echo "<div class='search_largeImg_header'>Large Image</div>";
			echo "<div class='search_mediumImg_header'>Medium Image</div>";
			echo "<div class='search_smallImg_header'>Small Image</div>";
			echo "<div class='search_noOfCopies_header'>No. of Copies</div>";
			echo "<div class='search_edit_header'>Edit</div>";
			echo "<div class='search_delete_header'>Delete</div>";
			echo "<div class='search_deleteAll_header'>Delete All</div>";
		echo "</div>";
	include('connection.php');
	$result = mysql_query("SELECT * FROM books
	WHERE $category LIKE '%$searchterm%'
		ORDER BY $order");
	
	while($row = mysql_fetch_array($result)){
		echo "<div class='search_row'>";
			echo "<div class='search_isbn'>" . $row['isbn'] . "</div>";
			echo "<div class='search_title'><a href='bookprofile.php?isbn=" . $row['isbn'] . "'>" . $row['title'] . "</a></div>";
			echo "<div class='search_titleLong'>" . $row['titleLong'] . "</div>";
			echo "<div class='search_authors'><a href='adminbook.php?searchterm=" . $row['authors'] . "&category=authors&state=1'>" . $row['authors'] . "</a></div>";
			echo "<div class='search_publisher'>" . $row['publisher'] . "</div>";
			echo "<div class='search_noOfPages'>" . $row['noOfPages'] . "</div>";
			echo "<div class='search_binding'>" . $row['binding'] . "</div>";
			echo "<div class='search_ddc'>" . $row['ddc'] . "</div>";
			echo "<div class='search_lcc'>" . $row['lcc'] . "</div>";
			echo "<div class='search_description'>";
				if($row['description'] != NULL){
					echo "Yes";
				}
			echo "</div>";
			echo "<div class='search_largeImg'>";
				if($row['largeImg'] != NULL){
					echo "Yes";
				}
			echo "</div>";
			echo "<div class='search_mediumImg'>";
				if($row['mediumImg'] != NULL){
					echo "Yes";
				}
			echo "</div>";
			echo "<div class='search_smallImg'>";
				if($row['smallImg'] != NULL){
					echo "Yes";
				}
			echo "</div>";
			echo "<div class='search_noOfCopies'>" . $row['noOfCopies'] . "</div>";
			echo "<div class='search_edit'><a href='adminbookedit.php?isbn=" . $row['isbn'] ."'>Edit</a></div>";
			echo "<div class='search_delete'><a href=''>Delete</a></div>";
			echo "<div class='search_deleteAll'><a href=''>Delete All</a></div>";
		echo "</div>";
	}
	
	echo "</div><!--End of search_table-->";
}
?>