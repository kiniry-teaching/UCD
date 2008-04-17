<?php
/****************************************************************
* 																*
* install() - 													*
* takes the host name, database username and password and		*
* database name and use them to access the database and create	*
* the tables necessary for the software to function.			*
* 																*
****************************************************************/

function install($host, $username, $password, $dbname, $awskey, $isbndbkey, $address){

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
	* Edits the config.txt file with the full path					*
	* 																*
	****************************************************************/

	$file = fopen("../config.txt","w");
	fwrite($file,"$address");
	fclose($file);

	chmod("../config.txt",0644);


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
		isbnUsername varchar(44) NOT NULL,
		PRIMARY KEY(isbnUsername),
		date int
	)";
	mysql_query($sql,$con);	
	
	$sql = 'DROP TABLE IF EXISTS `books_requests`';
	mysql_query($sql,$con);	

	$sql = "CREATE TABLE books_requests 
	(
		isbnUsername varchar(44) NOT NULL,
		PRIMARY KEY(isbnUsername)
	)";
	mysql_query($sql,$con);	
	
	$sql = 'DROP TABLE IF EXISTS `books_returned`';
	mysql_query($sql,$con);	
	
	$sql = "CREATE TABLE books_returned 
	(
		isbnUsername varchar(44) NOT NULL,
		PRIMARY KEY(isbnUsername)
	)";
	mysql_query($sql,$con);	
	
	$sql = 'DROP TABLE IF EXISTS `books_reviews`';
	mysql_query($sql,$con);	
	
	$sql = "CREATE TABLE books_review 
	(
		isbnUsername varchar(44) NOT NULL,
		PRIMARY KEY(isbnUsername),
		rating int(5),
		review text
	)";
	mysql_query($sql,$con);	

	/*
	*	create user systems tables
	*	added: 19/3/08
	*/
	$sql = 'DROP TABLE IF EXISTS `users`';
	mysql_query($sql,$con);	

	$sql =	"CREATE TABLE users (
 		username varchar(30),
		PRIMARY KEY(username), 
 		password varchar(32),
 		userlevel tinyint(1) unsigned not null,
 		email varchar(50),
 		timestamp int(11) unsigned not null
	)";
	mysql_query($sql,$con);	

	$sql = 'DROP TABLE IF EXISTS `users_online`';
	mysql_query($sql,$con);	

	$sql =	"CREATE TABLE users_online (
 		username varchar(30),
		PRIMARY KEY(username),
 		timestamp int(11) unsigned not null
	)";
	mysql_query($sql,$con);	
	
		$sql = 'DROP TABLE IF EXISTS `users_friends`';
	mysql_query($sql,$con);	

	$sql =	"CREATE TABLE users_friends (
 		username varchar(30),
		PRIMARY KEY(username),
 		friend varchar(30),
		timestamp int(11) unsigned not null
	)";

	mysql_query($sql,$con);	
	
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