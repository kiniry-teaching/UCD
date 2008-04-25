<?php

/*
This method should get all the common movies (i.e. a list of all the movies
that both profiles contain (have rated!) between the current profile and the profile &#65533;other&#65533;.
*/
function getCommonBooks($username1, $username2){
	$user1Array = array();
	$user2Array = array();
	
	include("connection.php"); //Connects to database

	$result = mysql_query("SELECT * FROM books_review
		WHERE username='$username1'");

	while($row = mysql_fetch_array($result)){
		if($row['isbn'] != NULL){
			array_push($user1Array, $row['isbn']);
		}
	}
	
	$result = mysql_query("SELECT * FROM books_review
		WHERE username='$username2'");

	while($row = mysql_fetch_array($result)){
		if($row['isbn'] != NULL){
			array_push($user2Array, $row['isbn']);
		}
	}
	
	$common = array_intersect($user1Array, $user2Array);
	return $common;
}

/*
* Computes the MSD similarity between 2 profiles.
*/

function computeMSDSimilarity($username1, $username2){
	$common = getCommonBooks($username1, $username2);
	
	$countSize = count($common);
	
	if($countSize!=0){
		$total=0;
		
		$isbn = current($common);
		for($i = 0 $i<$countSize; $i++){
			$rating1 = 0; $rating2 = 0;
			
			include("connection.php"); //Connects to database			
			
			$result = mysql_query("SELECT * FROM books_review
				WHERE username='$username1' AND isbn='$isbn'");
		
			while($row = mysql_fetch_array($result)){
				$rating1 = $row['rating'];
			}
			
			$result = mysql_query("SELECT * FROM books_review
				WHERE username='$username2' AND isbn='$isbn'");
		
			while($row = mysql_fetch_array($result)){
				$rating2 = $row['rating'];
			}
			
			total += ($rating1 - $rating2) * ($rating1 - $rating2);
			
			$isbn = next($common);
		}
		
		return $total/$countSize;
	}
	else{
		return 0;
	}
}

/*
Computes the pearson correlation coefficent (similarity) between 2 profiles.
*/
function computePearsonSimilarity($username1, $username2){
	$mean1 = getMeanRating($username1);
	$mean2 = getMeanRating($username2);
	$common = getCommonBooks($username1, $username2);

	$countSize = count($common);
	
	if($countSize!=0){
		$top = 0;
		$sumSqurTotal1 = 0;
		$sumSqurTotal2 = 0;
		
		$isbn = current($common);
		for($i = 0 $i<$countSize; $i++){
			$rating1 = 0;
			$rating2 = 0;
			
			include("connection.php"); //Connects to database
					
			$result = mysql_query("SELECT * FROM books_review
				WHERE username='$username1' AND isbn='$isbn'");
		
			while($row = mysql_fetch_array($result)){
				$rating1 = $row['rating'];
			}
			
			$result = mysql_query("SELECT * FROM books_review
				WHERE username='$username2' AND isbn='$isbn'");
		
			while($row = mysql_fetch_array($result)){
				$rating2 = $row['rating'];
			}
			
			$diff1 = $rating1 - $mean1;
			$diff2 = $rating2 - $mean2;
			
			$top += $diff1*$diff2;
			$sumSqurTotal1 += ($rating1 - $mean1)*($rating1 - $mean1);
			$sumSqurTotal2 += ($rating2 - $mean2)*($rating2 - $mean2);
			
			$isbn = next($common);
		}
		
		$bottom = sqrt($sumSqurTotal1*$sumSqurTotal2);
		
		return $top/$bottom;
	}
	else{
		return 0;
	}
}

/*
Predicts the rating for a movie for the given profile using the MSD metric
*/
function predictMSDRating($username, $isbn, $threshold){
	$neighbours = computeMSDNeighbours($username, $threshold);
	$top=0;
	$bottom=0;
	
	$countSize = count($neighbours);
	
	$isbn = current($neighbours);
	
	include("connection.php"); //Connects to database
	
	for($i = 0 $i<$countSize; $i++){
		$result = mysql_query("SELECT * FROM books_review
			WHERE isbn='$isbn'");
	
		while($row = mysql_fetch_array($result)){
			$w = ($threshold - computeMSDSimilarity($username, $row['username']))/$threshold;
			
			$top += $w*$row['rating'];
			$bottom += $w;
		}

		$isbn = next($neighbours);
	}
	
	if($bottom>0){
		return $top/$bottom;
	}
	return 0;
}
/*
Computes the set of neighbours that will be used in the prediction of a movie rating for a given user.
Note that its suggested that you implement this method but not necessary
*/
function computeMSDNeighbours($username, $threshold){
	$neighbours = array();
	
	include("connection.php"); //Connects to database
	
	$result = mysql_query("SELECT * FROM books_review");

	while($row = mysql_fetch_array($result)){
		if($row['username'] != $username){
			$msd = computeMSDSimilarity($username, $row['username']);
			if($msd != 0 && $msd <= $threshold){
				array_push($row['username']);
			}
		}
	}
	
	return $neighbours;
}

/*
Predicts the rating for a movie for the given profile using the Pearson similarity metric
*/
function predictPearsonRating($username, $isbn, $threshold){
	$neighbours = computeMSDNeighbours($username, $threshold);
	$top=0;
	$bottom=0;
	
	$countSize = count($neighbours);
	
	$isbn = current($neighbours);
	
	include("connection.php"); //Connects to database
	
	for($i = 0 $i<$countSize; $i++){
		$result = mysql_query("SELECT * FROM books_review
			WHERE isbn='$isbn'");
	
		while($row = mysql_fetch_array($result)){
			$w = computePearsonSimilarity($username, $row['username']);
			
			$top += $w*($row['rating']-getMeanRating($row['rating']);
			$bottom += abs($w);
		}

		$isbn = next($neighbours);
	}
	
	if($bottom==0){
		return 0;
	}
	return getMeanRating($username)+($top/$bottom);
}

/*
Computes the set of neighbours that will be used in the prediction of a movie rating for a given user.
Note that its suggested that you implement this method but not necessary
*/
function computePearsonNeighbours($username, $threshold){
	$neighbours = array();
	
	include("connection.php"); //Connects to database
	
	$result = mysql_query("SELECT * FROM books_review");

	while($row = mysql_fetch_array($result)){
		if($row['username'] != $username){
			$msd = computeMSDSimilarity($username, $row['username']);
			if($msd != 0 && $msd >= $threshold){
				array_push($row['username']);
			}
		}
	}
	
	return $neighbours;
}

function getMeanRating($username){
	$total=0;
	$number=0;
	
	include("connection.php"); //Connects to database

	$result = mysql_query("SELECT * FROM books_review
		WHERE username='$username'");

	while($row = mysql_fetch_array($result)){
		if($row['isbn'] != NULL){
			$total += $row['rating'];
			$number++;
		}
	}

	return $total/$number;
}

?>