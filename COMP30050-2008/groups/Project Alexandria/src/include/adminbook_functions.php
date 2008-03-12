<?php

//TODO - Thomas - isAdmin() needed here

/****************************************************************
* 																*
* Global array containg all variables necessary for the			*
* addition and editing of books.								*
* 																*
****************************************************************/
$bookData = array(
	$isbn,
	$title,
	$titleLong,
	$authors,
	$publisher,
	$noOfPages,
	$binding,
	$ddc,
	$lcc,
	$description,
	$largeImg,
	$mediumImg,
	$smallImg
);

include("config.php"); //Holds the access keys for the API's

function fetchBooks($isbn){
	
}


function addBook($bookData){

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

	include("connection.php");
	$sql="INSERT INTO books (isbn,title,titleLong,authors,publisher,noOfPages,binding,ddc,lcc,description,largeImg,mediumImg,smallImg)
		VALUES ('$isbn','$title','$titleLong','$authors','$publisher','$noOfPages','$binding','$ddc','$lcc','$description','$largeImg','$mediumImg','$smallImg')";
	if (!mysql_query($sql,$con))
	{
		die('Error: ' . mysql_error());
	}
	echo "<p>1 record added</p>";
	mysql_close($con);
}
?>