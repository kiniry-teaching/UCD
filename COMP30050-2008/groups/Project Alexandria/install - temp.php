<?php

DROP TABLE IF EXISTS users;

CREATE TABLE users (
 username varchar(30) primary key,
 password varchar(32),
 userlevel tinyint(1) unsigned not null,
 email varchar(50),
 timestamp int(11) unsigned not null
);

DROP TABLE IF EXISTS users_online;

CREATE TABLE users_online (
 username varchar(30) primary key,
 timestamp int(11) unsigned not null
);

?>