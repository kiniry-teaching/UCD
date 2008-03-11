<?php

//TODO - Thomas - isAdmin() needed here

/****************************************************************
* 																*
* Global variables necessary for the addition and editing of	*
* books.														*
* 																*
****************************************************************/
$authors =		"";
$binding =		"";
$ddc =			"";
$description =	"";
$isbn =			"";
$largeImg =		"";
$lcc =			"";
$mediumImg =	"";
$noOfPages =	"";
$publisher =	"";
$smallImg =		"";
$title =		"";
$titleLong =	"";

include("config.php"); //Holds the access keys for the API's

function fetchBooksAmazon($isbn, $j){
	$amazons = array("http://webservices.amazon.com/onca/xml?Service=AWSECommerceService", "http://webservices.amazon.co.uk/onca/xml?Service=AWSECommerceService", "http://webservices.amazon.co.jp/onca/xml?Service=AWSECommerceService", "http://webservices.amazon.fr/onca/xml?Service=AWSECommerceService", "http://webservices.amazon.ca/onca/xml?Service=AWSECommerceService", "http://webservices.amazon.de/onca/xml?Service=AWSECommerceService");
	$responceGroup = array("Small", "ItemAttributes", "Images", "EditorialReview");

	for ($i=0; $i<count($responceGroup); $i++){
		$requestURL = "" . $amazons[$j] . "&AWSAccessKeyId=" . KEYID . "&Operation=ItemLookup&ItemId=" . $isbn . "&Version=2007-07-16&ResponseGroup=" . $responceGroup[$i];

		$request = file_get_contents($requestURL);

		switch ($i){
			case 0: $basicDetails = simplexml_load_string($request); break;
			case 1: $attributes = simplexml_load_string($request); break;
			case 2: $images = simplexml_load_string($request); break;
			case 3: $review = simplexml_load_string($request); break;
		}
		
	}

	if($basicDetails->Items->Request->Errors->Error->Code == "AWS.InvalidParameterValue" && $j<count($amazons)-1){
		$j++;
		fetchBooksAmazon($isbn, $j);
	}
	else if($basicDetails->Items->Request->Errors->Error->Code == "AWS.InvalidParameterValue" && $j=count($amazons)-1){
		fetchBooksISBNdb($isbn);
	}
	else if($basicDetails->Items->Request->Errors->Error->Code != "AWS.InvalidParameterValue" && $j=count($amazons)-1){	
		printDetailsAmazon($basicDetails, $attributes, $images, $review);
	}
}

function printDetailsAmazon($basicDetails, $attributes, $images, $review){
	global $smallImg,
	$mediumImg,
	$largeImg,
	$title,
	$authors,
	$binding,
	$noOfPages,
	$description;
	
	$smallImg =		$images->Items->Item->SmallImage->URL;
	$mediumImg =	$images->Items->Item->MediumImage->URL;
	$largeImg =		$images->Items->Item->LargeImage->URL;
	$title =		$basicDetails->Items->Item->ItemAttributes->Title;
	$authors =		$basicDetails->Items->Item->ItemAttributes->Author;
	$binding =		$attributes->Items->Item->ItemAttributes->Binding;
	$noOfPages =	$attributes->Items->Item->ItemAttributes->NumberOfPages;
	$description =	$review->Items->Item->EditorialReviews->EditorialReview->Content;
}

function fetchBooksISBNdb($isbn){
	$resultsArgs = array("details", "texts");
	
	for ($i=0; $i<count($resultsArgs); $i++){
		$requestURL = "http://isbndb.com/api/books.xml?access_key=" . ACCESSKEY . "&results=" . $resultsArgs[$i] . "&index1=isbn&value1=" . $isbn;

		$request = file_get_contents($requestURL);
		
		switch ($i){
			case 0: $basicDetails = simplexml_load_string($request); break;
			case 1: $descriptions =  simplexml_load_string($request); break;
		}
	}
	
	printDetailsISBNdb($basicDetails, $descriptions);
}

function printDetailsISBNdb($basicDetails, $descriptions){
	global $isbn,
	$title,
	$titleLong,
	$authors,
	$publisher,
	$ddc,
	$lcc,
	$description;
	$noOfPages;
	$binding;
	
	$isbn =			$basicDetails->BookList[0]->BookData[0]['isbn'];
	$title =		$basicDetails->BookList[0]->BookData[0]->Title;
	$titleLong =	$basicDetails->BookList[0]->BookData[0]->TitleLong;
	$authors =		$basicDetails->BookList[0]->BookData[0]->AuthorsText;
	$publisher =	$basicDetails->BookList[0]->BookData[0]->PublisherText;
	$ddc =			$basicDetails->BookList[0]->BookData[0]->Details[0]['dewey_decimal_normalized'];
	$lcc =			$basicDetails->BookList[0]->BookData[0]->Details[0]['lcc_number'];
	$description =	$descriptions->BookList[0]->BookData[0]->Summary;
	$noOfPages = 	$basicDetails->BookList[0]->BookData[0]->Details[0]['physical_description_text'];
	$binding =		$basicDetails->BookList[0]->BookData[0]->Details[0]['edition_info'];
}

function addBook(
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
	){
	
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