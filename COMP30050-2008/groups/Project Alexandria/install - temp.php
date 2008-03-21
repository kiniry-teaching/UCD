<?php

	/*
	*	create user systems tables
	*	added: 19/3/08
	*/
	$sql = 'DROP TABLE IF EXISTS `users`';
	mysql_query($sql,$con);	

	$sql =	"CREATE TABLE users (
 		username varchar(30) primary key,
 		password varchar(32),
 		userlevel tinyint(1) unsigned not null,
 		email varchar(50),
 		timestamp int(11) unsigned not null
	)";


	$sql = 'DROP TABLE IF EXISTS `users_online`';
	mysql_query($sql,$con);	

	$sql =	"CREATE TABLE users_online (
 		username varchar(30) primary key,
 		timestamp int(11) unsigned not null
	)";

?>