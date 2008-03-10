<?php
	include("include/header.php");
?>
<?php

//Enter your IDs
define("Access_Key_ID", "0W1AQXQJAVFWQFCAKRR2");
define("Associate_tag", "projecalexan-20");

//Set up the operation in the request
function ItemSearch($SearchIndex, $Keywords){

//Set the values for some of the parameters.
$Operation = "ItemSearch";
$Version = "2007-07-16";
$ResponseGroup = "ItemAttributes,Offers";
//User interface provides values 
//for $SearchIndex and $Keywords

//Define the request
$request=
     "http://ecs.amazonaws.com/onca/xml"
   . "?Service=AWSECommerceService"
   . "&AssociateTag=" . Associate_tag
   . "&AWSAccessKeyId=" . Access_Key_ID
   . "&Operation=" . $Operation
   . "&Version=" . $Version
   . "&SearchIndex=" . $SearchIndex
   . "&Keywords=" . $Keywords
   . "&ResponseGroup=" . $ResponseGroup;

//Catch the response in the $response object
$response = file_get_contents($request);
$parsed_xml = simplexml_load_string($response);
printSearchResults($parsed_xml, $SearchIndex);
}
?>
<table align='left'>
<?php 
    print("
      <form name='SearchTerms' action=adminbookadd.php method='GET'>
      <tr><td valign='top'>
        <b>Choose a Category</b><br>
          <select name='SearchIndex'>
            <option value='Books'>Books</option>
            <option value='DVD'>DVD</option>
            <option value='Music'>Music</option>
          </select>
      </td></tr>
      <tr><td><b>Enter Keywords</b><br><input type='text' name='Keywords' size='40'/></td></tr>
      <input type='hidden' name='Action' value='Search'>
      <input type='hidden' name='CartId' value=$CartId>
      <input type='hidden' name='HMAC' value=$HMAC>
      <tr align='center'><td><input type='submit'/></td></tr>
      </form> ");
?>
</table>
<?php
function printSearchResults($parsed_xml, $SearchIndex){
  print("<table>");
  $numOfItems = $parsed_xml->Items->TotalResults;
  if($numOfItems>0){
  foreach($parsed_xml->Items->Item as $current){
    print("<td><font size='-1'><b>".$current->ItemAttributes->Title."</b>");
    if (isset($current->ItemAttributes->Title)) {
    print("<br>Title: ".$current->ItemAttributes->Title);
  } elseif(isset($current->ItemAttributes->Author)) {
    print("<br>Author: ".$current->ItemAttributes->Author);
  } elseif 
   (isset($current->Offers->Offer->Price->FormattedPrice)){
    print("<br>Price:
    ".$current->Offers->Offer->Price->FormattedPrice);
  }else{
  print("<center>No matches found.</center>");
   }
  }
 }
}
?>
<?php
	include("include/footer.php");
?>