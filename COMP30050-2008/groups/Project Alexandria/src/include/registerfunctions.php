<?php
function check($username, $email1, $email2, $password1, $password2)
	{
		/************************************************************************/	
		/*	check()																*/
		/*	runs a check to ensure the entered username 						*/
		/*	is not already in the database										*/
		/*	if it does not then the emails are checked to see if they match		*/
		/*	if they do then the passwords are checked to see if they match		*/
		/*	if everything is correct then the method returns True				*/
		/************************************************************************/
		
		
		if(strlen($username) == 0)
		{
		echo("<p>Username field is empty, please enter a username</p>");
		return False;
		}
				if(strlen($username) > 30)
		{
		echo("<p>The Username ".$username." is too long!<br /> 
		Please Try a username that is less than 30 character long. </p>");
		return False;
		}
		else
		{
			include("connection.php"); //Connects to database
			$result = mysql_query("SELECT * FROM users	
			WHERE username ='$username'");
			$ANOTHER_VARIABLE = mysql_num_rows($result);
			if($ANOTHER_VARIABLE != 0)
				{
				echo "<p>The username ". $username ." already exists, please try another username</p>";
				return False;
				}
			else if($email1 != $email2) //compares the two entered email addresses
				{
				echo "e-mail addresses do not match, please try again.<br />";
				return False;
				}
			else 
			
			if(strpos($email1,"@")==False&& strpos($email1,".")==False )
				//checks to see if the e-mail address contains @ and . /
				{
				echo ($email1." is not a valid e-mail address, please try again.<br />");
				return False;
				}
			else
						
			if($password1 != $password2) //compares the two entered passwords
				{
				echo "Passwords do not match, please try again.<br />";
				return False;
				}
			else
			if(strlen($password1) > 32)
			{
			echo("<p>The Password is too long!<br /> 
			Please Try a password that is shorter than 32 character. </p>");
			return False;
			}
			if(strlen($password1) < 5)
			{
			echo("<p>That Password is too short!<br /> 
			Please Try a password that is longer than 5 character. </p>");
			return False;
			}
			else
			{return True;}
		}
	}/*	check()	*/	

function checkUsername($username)
	{
		/************************************************************************/	
		/*	checkUsername() 														*/
		/*	sets the userlevel to 1(standard user) 								*/
		/*	if the username given is ADMIN,										*/
		/*	that user is given the admin userlevel								*/
		/*	the ADMIN user level allows access to the adminfunctions			*/
		/************************************************************************/

		if($username=="admin")
		{return "9";}else{return "1";}
	}/*checkUsername()*/
	

function createUser($username, $password1, $userlevel, $email1, $email2, $password1, $password2)
	{	
		/************************************************************************/	
		/*	createUser 															*/
		/*	creates a new entry in the users database using the given details	*/
		/************************************************************************/
	
	if(check($username, $email1, $email2, $password1, $password2)==True)
		{
		//test
		$userlevel = checkUsername($username);
		include("connection.php"); //Connects to database
		
		$md5pass = md5($password1);  //hash function to encrypt the password before adding it to the database
		$date=date('d-F-Y'); //add todays date to the datebase as the date of registration
		//$time=time();
		$sql="INSERT INTO users (username, password, userlevel, email, date)
								VALUES ('$username', '$md5pass', '$userlevel', '$email1', '$date')";
			if (!mysql_query($sql,$con))
			{
			die('Error: ' . mysql_error());
			}
		echo ("Account registered for ".$username."!<br />");		
		}
		else{echo("<b>Registration Failed!</b><br />");}
		
	}/*createUser*/

?>