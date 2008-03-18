<?php
	include("include/header.php");
?>
<div id="adminbookedit">
<?php
//TODO - Thomas - isAdmin() needed here
include("include/book_functions.php");
include("include/adminbook_functions.php");
$isbn = $_GET["isbn"];
fetchBookFromDB($isbn);

if ($_POST["state"] == 1){ //If you're editing book data
	$title = $_POST['title']; $titleLong = $_POST['titleLong']; $authors = $_POST['authors']; $publisher = $_POST['publisher']; $noOfPages = $_POST['noOfPages']; $binding = $_POST['binding']; $ddc = $_POST['ddc']; $lcc = $_POST['lcc']; $description = $_POST['description']; $largeImg = $_POST['largeImg']; $mediumImg = $_POST['mediumImg']; $smallImg = $_POST['smallImg']; $noOfCopies = $_POST['noOfCopies'];
	updateBook();
}
?>
	<h1>Edit A Book</h1>
	<form action="adminbookedit.php<?php echo "?isbn=".$isbn?>" method="post">
		<div class="formrow"><div class="formtext">ISBN: </div><div class="forminput"><p><?php echo $isbn; ?></p></div></div>
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
		<div class="formrow"><div class="formtext">Number of Copies: </div><div class="forminput"><input type="text" name="noOfCopies" value="1" /></div></div>
		<div class="formbutton"><input type="hidden" name="state" value="1" /><input type="submit" value="Edit" /></div>
	</form>

</div> <!--End of #adminbookedit-->
<?php
	include("include/footer.php");
?>