
<?php
login($enteredUsername, $enteredPassword)

/*	Master method for Login
	This method will call checkMatch, 
	which will in turn call checkName() & checkPassword()
*/
{
}

checkMatch($enteredUsername, $enteredPassword)
/*
compares the username and the password that were entered to see if they match thos stored in tha daqtabase
*/

checkName($enteredUsername){}
checkPassword($username, $enteredUsername){}
getName($enteredUsername){} //may be completely useless as the comparison should be covered by checkName()
getPassword($enteredUsername){}


?>