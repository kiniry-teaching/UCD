<?php
function sendEmailBookDue(){
	include("connection.php"); //Connects to the database

	$test="";
	
	$result = mysql_query("SELECT * FROM books_onloan
		WHERE date<='$sendTime'");
	
	while($row = mysql_fetch_array($result)){
		$test = $row['isbnUsername'];
	}
	
	if($test != NULL){
	
		$messages = array();
		
		$maxTime = 0; //TODO - Amal - Get the max time set by the admin for a book to be out
		$warningTime = 0; //TODO - Amal - Get the warning time set by the admin for an alert ahead of a book being due
		$currentTime = time();
		
		$sendTime = $currentTime - $maxTime - $warningTime;
		
		$result = mysql_query("SELECT * FROM books_onloan
			WHERE date<='$sendTime'");
	
		while($row = mysql_fetch_array($result)){
			$isbnUsername = $row['isbnUsername'];
			$array = (explode(" ",$isbnUsername));
			
			$isbn = current($array);
			$title="";
			
			$result2 = mysql_query("SELECT * FROM books
				WHERE isbn='$isbn'");
	
			while($row = mysql_fetch_array($result2)){
				$title = $row['title'];
			}
	
			$username = end($array);
			$dueDate = $row['date'] + $maxTime;
			$dueDatePrint = date("d/m/Y", $dueDate);
			
			$message = $username . " has " . $title . " due by " . $dueDatePrint".<br />";
			array_push($messages,$message);
		}
		
		$result = mysql_query("SELECT * FROM users
			WHERE userlevel='8'");
		
		while($row = mysql_fetch_array($result)){
			$to = $row['email'];
			$subject = "Book(s) Due";
			$message = "Hello" . $row['username']. ",<br />The following are due;<br />" . array_reduce($messages,"reduceMessages");
			
			$adminEmail="";
			
			$result2 = mysql_query("SELECT * FROM users
				WHERE username='admin'");
			
			while($row = mysql_fetch_array($result2)){
				$adminEmail = $row['email'];
			}
	
			$from = $adminEmail;
			$headers = "From: $from";
			mail($to,$subject,$message,$headers);
		}
	}
}

function reduceMessages($v1,$v2){
	return $v1 . $v2;
}

sendEmailBookDue();
?>