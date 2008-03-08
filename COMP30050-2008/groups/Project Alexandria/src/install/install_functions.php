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
	<?php
		\$con=mysql_connect ($host, $username, $password)
			or die
				('I cannot connect to the database because: ' . mysql_error());
		mysql_select_db ($dbname, \$con);
	?" . ">");
	fclose($file);

	chmod("../connection.php",0644);
	
	$con=mysql_connect ($host, $username, $password)
			or die
				('I cannot connect to the database because: ' . mysql_error());
	mysql_select_db ($dbname, $con);
	
	$sql = "CREATE TABLE books 
	(
		isbn int(13)
	)";
	mysql_query($sql,$con);
	//TODO - Ryan - Create tables
	//TODO - Thomas - Create tables	
	
	echo "<p>Installation Complete</p>";
}
?>