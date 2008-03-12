<?php
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
	global $bookData;
	
	if($isbn == NULL)
		$isbn =			$basicDetails->BookList[0]->BookData[0]['isbn'];
	if($title == NULL)
		$title =		$basicDetails->BookList[0]->BookData[0]->Title;
	if($titleLong == NULL)
		$titleLong =	$basicDetails->BookList[0]->BookData[0]->TitleLong;
	if($authors == NULL)
		$authors =		$basicDetails->BookList[0]->BookData[0]->AuthorsText;
	if($publisher == NULL)
		$publisher =	$basicDetails->BookList[0]->BookData[0]->PublisherText;
	if($ddc == 0)
		$ddc =			$basicDetails->BookList[0]->BookData[0]->Details[0]['dewey_decimal_normalized'];
	if($lcc == NULL)
		$lcc =			$basicDetails->BookList[0]->BookData[0]->Details[0]['lcc_number'];
	if($description == NULL)
		$description =	$descriptions->BookList[0]->BookData[0]->Summary;
	if($noOfPages == NULL)
		$noOfPages = 	$basicDetails->BookList[0]->BookData[0]->Details[0]['physical_description_text'];
	if($binding == NULL)
		$binding =		$basicDetails->BookList[0]->BookData[0]->Details[0]['edition_info'];
}

?>