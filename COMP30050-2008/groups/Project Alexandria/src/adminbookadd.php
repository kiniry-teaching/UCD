<?php
	include("include/header.php");
?>
<div id="adminbookedit">
<?php

//TODO - Thomas - isAdmin() needed here

include("include/adminbook_functions.php");

if ($_POST["state"] == 1){ //If you're retrieving book data
	$isbn = $_POST["isbn"];
	fetchBooks($isbn);
	parseBookData();
}
else if($_POST["state"] == 2) //If you're adding book data
	addBook($_POST["isbn"],$_POST["title"],$_POST["titleLong"],$_POST["authors"],$_POST["publisher"],$_POST["noOfPages"],$_POST["binding"],$_POST["ddc"],$_POST["lcc"],$_POST["description"],$_POST["largeImg"],$_POST["mediumImg"],$_POST["smallImg"], $_POST["noOfCopies"]);
?>
	<h1>Add A Book</h1>
	<ol>
		<li>Enter the ISBN below and click "Retrieve".</li>
		<li>The details will appear in the form below for you to edit and approve.</li>
		<li>When you're happy just click "Add".</li>
	</ol>
	<ul>
		<li>If no details appear you can add them manually.</li>
	</ul>
	<form action="adminbookadd.php" method="post">
		<div class="formrow"><div class="formtext">ISBN: </div><div class="forminput"><input type="text" name="isbn" /></div></div>
		<div class="formbutton"><input type="hidden" name="state" value="1" /><input type="submit" value="Retrieve" /></div>
	</form>
	<form action="adminbookadd.php" method="post">
		<div class="formrow"><div class="formtext">ISBN: </div><div class="forminput"><input type="text" name="isbn" value="<?php echo $isbn; ?>" /></div></div>
		<div class="formrow"><div class="formtext">Title: </div><div class="forminput"><input type="text" name="title" value="<?php echo $title; ?>" /></div></div>
		<div class="formrow"><div class="formtext">Title (Long): </div><div class="forminput"><input type="text" name="titleLong" value="<?php echo $titleLong; ?>" /></div></div>
		<div class="formrow"><div class="formtext">Authors: </div><div class="forminput"><input type="text" name="authors" value="<?php echo $authors; ?>" /></div></div>
		<div class="formrow"><div class="formtext">Publisher: </div><div class="forminput"><input type="text" name="publisher" value="<?php echo $publisher; ?>" /></div></div>
		<div class="formrow"><div class="formtext">DDC: </div><div class="forminput"><input type="text" name="ddc" value="<?php echo $ddc; ?>" /></div></div>
		<div class="formrow"><div class="formtext">LCC: </div><div class="forminput"><input type="text" name="lcc" value="<?php echo $lcc; ?>" /></div></div>
		<div class="formrow"><div class="formtext">Binding: </div><div class="forminput"><input type="text" name="binding" value="<?php echo $binding; ?>" /></div></div>
		<div class="formrow"><div class="formtext">Number of Pages: </div><div class="forminput"><input type="text" name="noOfPages" value="<?php echo $noOfPages; ?>" /></div></div>
		<div class="formrow"><div class="formtext">Small Image URL: </div><div class="forminput"><input type="text" name="smallImg" value="<?php echo $smallImg; ?>" /></div></div>
		<div class="formrow"><div class="formtext">Medium Image URL: </div><div class="forminput"><input type="text" name="mediumImg" value="<?php echo $mediumImg; ?>" /></div></div>
		<div class="formrow"><div class="formtext">Large Image URL: </div><div class="forminput"><input type="text" name="largeImg" value="<?php echo $largeImg; ?>" /></div></div>
		<div class="formrow"><div class="formtext">Description: </div><div class="forminput"><textarea name="description"><?php echo $description; ?></textarea></div></div>
		<div class="formrow"><div class="formtext">Number of Copies: </div><div class="forminput"><input type="text" name="noOfCopies" value="Enter number" /></div></div>
		<div class="formbutton"><input type="hidden" name="state" value="2" /><input type="submit" value="Add" /></div>
	</form>
</div> <!--End of #adminbookedit-->
<?php
	include("include/footer.php");
?>