<?php
/****************************************************************
* 																*
* install() - 													*
* takes the host name, database username and password and		*
* database name and use them to access the database and create	*
* the tables necessary for the software to function.			*
* 																*
****************************************************************/

function install($host, $username, $password, $dbname){

	/****************************************************************
	* 																*
	* Edits the connection.php file with the connection data and	*
	* function that will be used through out the software.			*
	* 																*
	****************************************************************/

	$file = fopen("../connection.php","w");
	fwrite($file,"
	<?php
		\$con=mysql_connect ($host, $username, $password)
			or die
				('I cannot connect to the database because: ' . mysql_error());
		mysql_select_db ($dbname, \$con);
	?" . ">");
	fclose($file);

	chmod("../connection.php",0644);

	/****************************************************************
	* 																*
	* Connects to the database										*
	* 																*
	****************************************************************/
	 	 	
	$con=mysql_connect ($host, $username, $password);
	if (!$con){
		die('Could not connect: ' . mysql_error());
	}
	mysql_select_db ($dbname, $con);

	/****************************************************************
	* 																*
	* Creates all the book related tables							*
	* 																*
	****************************************************************/

	$sql = 'DROP TABLE IF EXISTS `books`';
	mysql_query($sql,$con);	
	
	$sql = "CREATE TABLE books 
	(
		isbn int(13) NOT NULL, 
		PRIMARY KEY(isbn),
		title tinytext,
		titleLong text,
		author tinytext,
		publisher tinytext,
		ddc decimal,
		description text
	)";
	mysql_query($sql,$con);	
	
	$sql = 'DROP TABLE IF EXISTS `books_onloan`';
	mysql_query($sql,$con);	

	$sql = "CREATE TABLE books_onloan 
	(
		loanNo bigint NOT NULL AUTO_INCREMENT, 
		PRIMARY KEY(loanNo),
		isbnUsername text,
		date int
	)";
	mysql_query($sql,$con);	
	
	$sql = 'DROP TABLE IF EXISTS `books_requests`';
	mysql_query($sql,$con);	

	$sql = "CREATE TABLE books_requests 
	(
		requestNo bigint NOT NULL AUTO_INCREMENT, 
		PRIMARY KEY(requestNo),
		isbnUsername text
	)";
	mysql_query($sql,$con);	
	
	$sql = 'DROP TABLE IF EXISTS `books_returned`';
	mysql_query($sql,$con);	
	
	$sql = "CREATE TABLE books_returned 
	(
		returnNo bigint NOT NULL AUTO_INCREMENT, 
		PRIMARY KEY(returnNo),
		isbnUsername text
	)";
	mysql_query($sql,$con);	
	
	$sql = 'DROP TABLE IF EXISTS `books_reviews`';
	mysql_query($sql,$con);	
	
	$sql = "CREATE TABLE books_review 
	(
		reviewNo bigint NOT NULL AUTO_INCREMENT, 
		PRIMARY KEY(reviewNo),
		isbnUsername text,
		rating int(5),
		review text
	)";
	mysql_query($sql,$con);	

	//TODO - Thomas - Create tables	
	
	/****************************************************************
	* 																*
	* Ends the installation.										*
	* 																*
	****************************************************************/
	
	if ($con){		
		mysql_close($con);
		echo "<p>Installation Complete</p>";
	}
}
?>