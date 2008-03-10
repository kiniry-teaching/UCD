<?php
	include("include/header.php");
?>
<?php
$authors =		"";
$binding =		"";
$dcc =			"";
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

if($_POST["isbn"] != NULL){

	define('KEYID','0W1AQXQJAVFWQFCAKRR2');
	define('ACCESSKEY','6XBPB534');
	
	$isbn = $_POST["isbn"];

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
		$dcc,
		$lcc,
		$description;
		$noOfPages;
		$binding;
		
		$isbn =			$basicDetails->BookList[0]->BookData[0]['isbn'];
		$title =		$basicDetails->BookList[0]->BookData[0]->Title;
		$titleLong =	$basicDetails->BookList[0]->BookData[0]->TitleLong;
		$authors =		$basicDetails->BookList[0]->BookData[0]->AuthorsText;
		$publisher =	$basicDetails->BookList[0]->BookData[0]->PublisherText;
		$dcc =			$basicDetails->BookList[0]->BookData[0]->Details[0]['dewey_decimal_normalized'];
		$lcc =			$basicDetails->BookList[0]->BookData[0]->Details[0]['lcc_number'];
		$description =	$descriptions->BookList[0]->BookData[0]->Summary;
		$noOfPages = 	$basicDetails->BookList[0]->BookData[0]->Details[0]['physical_description_text'];
		$binding =		$basicDetails->BookList[0]->BookData[0]->Details[0]['edition_info'];
	}
	
	fetchBooksAmazon($isbn, 0);
}
?>
<div id="adminbookedit">
	<form action="bookdetailstest.php" method="post">
		<div class="formrow"><div class="formtext">ISBN: </div><div class="forminput"><input type="text" name="isbn" /></div></div>
		<div class="formbutton"><input type="submit" value="Retrieve" /></div>
	</form>
	<form action="bookdetailstest.php" method="post">
		<div class="formrow"><div class="formtext">ISBN: </div><div class="forminput"><input type="text" name="isbn" value="<?php echo $isbn; ?>" /></div></div>
		<div class="formrow"><div class="formtext">Title: </div><div class="forminput"><input type="text" name="title" value="<?php echo $title; ?>" /></div></div>
		<div class="formrow"><div class="formtext">Title (Long): </div><div class="forminput"><input type="text" name="titleLong" value="<?php echo $titleLong; ?>" /></div></div>
		<div class="formrow"><div class="formtext">Authors: </div><div class="forminput"><input type="text" name="authors" value="<?php echo $authors; ?>" /></div></div>
		<div class="formrow"><div class="formtext">Publisher: </div><div class="forminput"><input type="text" name="publisher" value="<?php echo $publisher; ?>" /></div></div>
		<div class="formrow"><div class="formtext">DCC: </div><div class="forminput"><input type="text" name="dcc" value="<?php echo $dcc; ?>" /></div></div>
		<div class="formrow"><div class="formtext">LCC: </div><div class="forminput"><input type="text" name="lcc" value="<?php echo $lcc; ?>" /></div></div>
		<div class="formrow"><div class="formtext">Binding: </div><div class="forminput"><input type="text" name="binding" value="<?php echo $binding; ?>" /></div></div>
		<div class="formrow"><div class="formtext">Number of Pages: </div><div class="forminput"><input type="text" name="noOfPages" value="<?php echo $noOfPages; ?>" /></div></div>
		<div class="formrow"><div class="formtext">Small Image URL: </div><div class="forminput"><input type="text" name="smallImg" value="<?php echo $smallImg; ?>" /></div></div>
		<div class="formrow"><div class="formtext">Medium Image URL: </div><div class="forminput"><input type="text" name="mediumImg" value="<?php echo $mediumImg; ?>" /></div></div>
		<div class="formrow"><div class="formtext">Large Image URL: </div><div class="forminput"><input type="text" name="largeImg" value="<?php echo $largeImg; ?>" /></div></div>
		<div class="formrow"><div class="formtext">Description: </div><div class="forminput"><textarea name="description" cols="20" rows="5"><?php echo $description; ?></textarea></div></div>
		<div class="formbutton"><input type="submit" value="Add" /></div>
	</form>
</div>
<?php
	include("include/footer.php");
?>