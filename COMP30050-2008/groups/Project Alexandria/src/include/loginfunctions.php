
<?php
login($enteredUsername, $enteredPassword)

/*	Master method for Login
*	This method will call checkMatch, 
*	which will in turn call checkName() & checkPassword()
*/
{
}

checkMatch($enteredUsername, $enteredPassword){
/*
*	compares the username and the password that were entered to see if they match those stored in the database
*/
}/*checkMatch*/

checkName($enteredUsername){
/*
* 	checks to see if the entered name exsists in the database
*	if it exsists the checkPassword method is called
*/
}/*checkName*/

checkPassword($username, $enteredUsername){
/*
*	checks to see if the entered password matches that which corresponds to the entered username
*/
}/*checkPassword*/

getName($enteredUsername){} //may not be needed
getPassword($enteredUsername){} //may not be needed

?>