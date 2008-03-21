<?php
	include("include/header.php");
?>
<div id="search">
	<?php 
		include('include/book_functions.php');
	?>
	<h1>Search</h1>
	<form action="search.php" method="get">
		<div class="formrow"><div class="formtext">Search Term: </div><div class="forminput"><input type="text" name="searchterm" /></div></div>
		<div class="formrow"><div class="formtext">Category: </div><div class="forminput">
			<select name="category">
				<option value="isbn">Pick a Category</option>
				<option value="isbn">ISBN</option>
				<option value="title">Title</option>
				<option value="titleLong">Title (Long)</option>
				<option value="authors">Author</option>
				<option value="publisher">Publisher</option>
				<option value="noOfPages">Number of Pages</option>
				<option value="binding">Binding</option>
			</select></div></div>
		<div class="formbutton"><input type="hidden" name="state" value="1" /><input type="submit" value="Search" /></div>
	</form>

	<?php 
		if($_GET['state'] == 1){
			tableOfBooks($_GET['searchterm'], $_GET['category'], 'title');
		}
		else if($_GET['state'] == 2){
			tableOfBooks($_GET['searchterm'], $_GET['category'], $_GET['order']);
		}
	?>

</div>
<?php
	include("include/footer.php");
?>