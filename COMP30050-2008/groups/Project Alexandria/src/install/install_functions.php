<?php
/****************************************************************
* 																*
* install() - 													*
* takes the host name, database username and password and		*
* database name and use them to access the database and create	*
* the tables necessary for the software to function.			*
* 																*
****************************************************************/

function install($host, $username, $password, $dbname, $awskey, $isbndbkey){

	/****************************************************************
	* 																*
	* Edits the connection.php file with the connection data and	*
	* function that will be used through out the software.			*
	* 																*
	****************************************************************/

	$file = fopen("../connection.php","w");
		if($password != NULL){
			fwrite($file,"
				<?php
					\$con=mysql_connect ($host, $username, $password)
						or die
							('I cannot connect to the database because: ' . mysql_error());
					mysql_select_db ($dbname, \$con);
				?" . ">");
		}
		else{
			fwrite($file,"
				<?php
					\$con=mysql_connect ($host, $username)
						or die
							('I cannot connect to the database because: ' . mysql_error());
					mysql_select_db ($dbname, \$con);
				?" . ">");

		}
	fclose($file);

	chmod("../connection.php",0644);
	
	/****************************************************************
	* 																*
	* Edits the config.php file with the keys for the API's			*
	* 																*
	****************************************************************/

	$file = fopen("../config.php","w");
	fwrite($file,"
	<?php
		define('KEYID','$awskey');
		define('ACCESSKEY','$isbndbkey');
	?" . ">");
	fclose($file);

	chmod("../config.php",0644);

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
		no bigint NOT NULL AUTO_INCREMENT, 
		PRIMARY KEY(no),
		isbn varchar(13) NOT NULL, 
		title tinytext,
		titleLong text,
		authors tinytext,
		publisher tinytext,
		ddc decimal,
		description text,
		noOfPages int,
		binding tinytext,
		lcc tinytext,
		largeImg tinytext,
		mediumImg tinytext,
		smallImg tinytext,
		noOfCopies bigint
	)";
	mysql_query($sql,$con);	
	
	$sql = 'DROP TABLE IF EXISTS `books_onloan`';
	mysql_query($sql,$con);	

	$sql = "CREATE TABLE books_onloan 
	(
		no int NOT NULL AUTO_INCREMENT, 
		PRIMARY KEY(no),
		isbn varchar(13) NOT NULL,
		username varchar(30) NOT NULL,
		date int
	)";
	mysql_query($sql,$con);	
	
	$sql = 'DROP TABLE IF EXISTS `books_requests`';
	mysql_query($sql,$con);	

	$sql = "CREATE TABLE books_requests 
	(
		no int NOT NULL AUTO_INCREMENT, 
		PRIMARY KEY(no),
		isbn varchar(13) NOT NULL,
		username varchar(30) NOT NULL
	)";
	
	mysql_query($sql,$con);	
	
	$sql = 'DROP TABLE IF EXISTS `books_returned`';
	mysql_query($sql,$con);	
	
	$sql = "CREATE TABLE books_returned 
	(
		no int NOT NULL AUTO_INCREMENT, 
		PRIMARY KEY(no),
		isbn varchar(13) NOT NULL,
		username varchar(30) NOT NULL
	)";
	
	mysql_query($sql,$con);	
	
	$sql = 'DROP TABLE IF EXISTS `books_reviews`';
	mysql_query($sql,$con);	
	
	$sql = "CREATE TABLE books_review 
	(
		no int NOT NULL AUTO_INCREMENT, 
		PRIMARY KEY(no),
		isbn varchar(13) NOT NULL,
		username varchar(30) NOT NULL,
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