<?php
/*
 * install() - 
 * takes the host name, database username and password and database name
 * and use them to access the database and create the tables necessary for
 * the software to function.
 */
function install($host, $username, $password, $dbname){
	$file = fopen("../connection.php","w");
	echo fwrite($file,"
		$dbh=mysql_connect ($host, $username, $password)
			or die
				('I cannot connect to the database because: ' . mysql_error());
		mysql_select_db ($dbname);");
	fclose($file);

	chmod("../connection.php",0644);
	
	//TODO - Ryan - Create tables
	//TODO - Thomas - Create tables	
	
	echo "<p>Installation Complete</p>";
}
?> 