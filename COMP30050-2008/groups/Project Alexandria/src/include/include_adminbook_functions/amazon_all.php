<?php
function fetchBooksAmazon($isbn, $j){
	$amazons = array("http://webservices.amazon.com/onca/xml?Service=AWSECommerceService",
					 "http://webservices.amazon.co.uk/onca/xml?Service=AWSECommerceService",
					 "http://webservices.amazon.co.jp/onca/xml?Service=AWSECommerceService",
					 "http://webservices.amazon.fr/onca/xml?Service=AWSECommerceService",
					 "http://webservices.amazon.ca/onca/xml?Service=AWSECommerceService",
					 "http://webservices.amazon.de/onca/xml?Service=AWSECommerceService");
	$responceGroup = array("Small", "ItemAttributes", "Images", "EditorialReview");

	for ($i=0; $i<count($responceGroup); $i++){
		$requestURL = $amazons[$j] . "&AWSAccessKeyId=" . KEYID . "&Operation=ItemLookup&ItemId=" . $isbn . "&Version=2007-07-16&ResponseGroup=" . $responceGroup[$i];

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
/*	else if($basicDetails->Items->Request->Errors->Error->Code == "AWS.InvalidParameterValue" && $j=count($amazons)-1){
		
	}*/
	else if($basicDetails->Items->Request->Errors->Error->Code != "AWS.InvalidParameterValue" && $j=count($amazons)-1){	
		printDetailsAmazon($basicDetails, $attributes, $images, $review);
	}
}

function printDetailsAmazon($basicDetails, $attributes, $images, $review){
	global $isbn, $bookData;
	
	for($j=0; $j<count($bookData); $j++){
		if($bookData[$j] == NULL){
			switch ($j){
/*isbn*/		case 0: $bookData[$j] =	$isbn; break;
/*title*/		case 1: $bookData[$j] =	$basicDetails->Items->Item->ItemAttributes->Title; break;
/*titleLong*/	case 2: break;
/*authors*/		case 3: $i=1;
						$bookData[$j] =	$basicDetails->Items->Item->ItemAttributes->Author;
						
						while($basicDetails->Items->Item->ItemAttributes->Author[$i] != NULL){
							$bookData[$j] =	$bookData[$j] . ", " . $basicDetails->Items->Item->ItemAttributes->Author[$i];
							$i++;
						}
						
						break;
/*publisher*/	case 4: break;
/*noOfPages*/	case 5: $bookData[$j] =	$attributes->Items->Item->ItemAttributes->NumberOfPages; break;
/*binding*/		case 6: $bookData[$j] =	$attributes->Items->Item->ItemAttributes->Binding; break;
/*ddc*/			case 7: break;
/*lcc*/			case 8: break;
/*description*/	case 9: $bookData[$j] =	$review->Items->Item->EditorialReviews->EditorialReview->Content; break;
/*largeImg*/	case 10: $bookData[$j] = $images->Items->Item->LargeImage->URL; break;
/*mediumImg*/	case 11: $bookData[$j] = $images->Items->Item->MediumImage->URL; break;
/*smallImg*/	case 12: $bookData[$j] = $images->Items->Item->SmallImage->URL; break;
			}
		}
	}

}
?>