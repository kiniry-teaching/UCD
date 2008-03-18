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
	global $isbn, $bookData;
	
	for($j=0; $j<count($bookData); $j++){
		if($bookData[$j] == NULL){
			switch ($j){
/*isbn*/		case 0: $bookData[$j] =	$isbn; break;
/*title*/		case 1: $bookData[$j] =	$basicDetails->BookList[0]->BookData[0]->Title; break;
/*titleLong*/	case 2: $bookData[$j] =	$basicDetails->BookList[0]->BookData[0]->TitleLong; break;
/*authors*/		case 3: $bookData[$j] =	$basicDetails->BookList[0]->BookData[0]->AuthorsText; break;
/*publisher*/	case 4: $bookData[$j] =	$basicDetails->BookList[0]->BookData[0]->PublisherText; break;
/*noOfPages*/	case 5: $bookData[$j] =	$basicDetails->BookList[0]->BookData[0]->Details[0]['physical_description_text']; break;
/*binding*/		case 6: $bookData[$j] =	$basicDetails->BookList[0]->BookData[0]->Details[0]['edition_info']; break;
/*ddc*/			case 7: $bookData[$j] =	$basicDetails->BookList[0]->BookData[0]->Details[0]['dewey_decimal_normalized'];break;
/*lcc*/			case 8: $bookData[$j] =	$basicDetails->BookList[0]->BookData[0]->Details[0]['lcc_number'];break;
/*description*/	case 9: $bookData[$j] =	$descriptions->BookList[0]->BookData[0]->Summary; break;
/*largeImg*/	case 10: break;
/*mediumImg*/	case 11: break;
/*smallImg*/	case 12: break;
			}
		}
	}
}
?>