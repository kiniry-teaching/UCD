<?php
	include("include/header.php");
?>
<div id="adminbook">
	<?php 
		include('include/adminbook_functions.php');
		
		if($_GET['delete'] == 1){
			deleteBook($_GET['isbn']);
		}
		else if($_GET['delete'] == "all"){
			deleteAllBook($_GET['isbn']);
		}
	?>
	<h1>Book Admin</h1>
	<p>
		<a href="adminbookadd.php">Add A Book</a>
	</p>
	<form action="adminbook.php" method="get">
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
				<option value="ddc">DDC</option>
				<option value="lcc">LCC</option>
			</select></div></div>
		<div class="formbutton"><input type="hidden" name="state" value="1" /><input type="submit" value="Search" /></div>
	</form>

	<?php 
		if($_GET['state'] == 1){
			adminTableOfBooks($_GET['searchterm'], $_GET['category'], 'title');
		}
		else if($_GET['state'] == 2){
			adminTableOfBooks($_GET['searchterm'], $_GET['category'], $_GET['order']);
		}
	?>
</div>
<?php
	include("include/footer.php");
?>