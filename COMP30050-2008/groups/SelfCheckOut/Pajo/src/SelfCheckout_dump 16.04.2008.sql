# CocoaMySQL dump
# Version 0.7b5
# http://cocoamysql.sourceforge.net
#
# Host: localhost (MySQL 5.0.51a)
# Database: SelfCheckout
# Generation Time: 2008-04-16 20:26:28 +0100
# ************************************************************

# Dump of table Customers
# ------------------------------------------------------------

CREATE TABLE `Customers` (
  `CustomerID` int(11) NOT NULL auto_increment,
  `Name` text,
  `EmailAddress` text,
  `PhoneNumber` int(11) default NULL,
  PRIMARY KEY  (`CustomerID`)
) ENGINE=MyISAM AUTO_INCREMENT=7 DEFAULT CHARSET=utf8;

INSERT INTO `Customers` (`CustomerID`,`Name`,`EmailAddress`,`PhoneNumber`) VALUES ('3','Bart Simpson','bart@gmail.com','5551234');
INSERT INTO `Customers` (`CustomerID`,`Name`,`EmailAddress`,`PhoneNumber`) VALUES ('2','Homer Simpson','homer@gmail.com','5553226');
INSERT INTO `Customers` (`CustomerID`,`Name`,`EmailAddress`,`PhoneNumber`) VALUES ('1','Patrick McDonagh','patrick.mcdonagh@gmail.com','2147483647');
INSERT INTO `Customers` (`CustomerID`,`Name`,`EmailAddress`,`PhoneNumber`) VALUES ('4','Joe Bloggs','joebloggsgmail.com','1234567');
INSERT INTO `Customers` (`CustomerID`,`Name`,`EmailAddress`,`PhoneNumber`) VALUES ('5','Gråinne Mulligan','grainnemulligan@gmail.com','123654');
INSERT INTO `Customers` (`CustomerID`,`Name`,`EmailAddress`,`PhoneNumber`) VALUES ('6','Peter V. Gibney','peter.gibney@ucdconnect.ie','1234575');


# Dump of table Items
# ------------------------------------------------------------

CREATE TABLE `Items` (
  `Barcode` bigint(20) NOT NULL default '0',
  `Name` tinytext NOT NULL,
  `Price` int(11) default NULL,
  `MinWeight` int(11) default NULL,
  `Weight` int(11) NOT NULL,
  `MaxWeight` int(11) default NULL,
  `SoundFileLoc` text,
  `ImageFileLoc` text,
  `Allergy` text,
  `PrimeItem` int(11) NOT NULL,
  PRIMARY KEY  (`Barcode`)
) ENGINE=MyISAM DEFAULT CHARSET=utf8;

INSERT INTO `Items` (`Barcode`,`Name`,`Price`,`MinWeight`,`Weight`,`MaxWeight`,`SoundFileLoc`,`ImageFileLoc`,`Allergy`,`PrimeItem`) VALUES ('1','Dairy Cheese','125','225','250','275',NULL,NULL,'Warning Contains Dairy','0');
INSERT INTO `Items` (`Barcode`,`Name`,`Price`,`MinWeight`,`Weight`,`MaxWeight`,`SoundFileLoc`,`ImageFileLoc`,`Allergy`,`PrimeItem`) VALUES ('2','Milk','100','450','500','550','','','Warning Contains Dairy','0');
INSERT INTO `Items` (`Barcode`,`Name`,`Price`,`MinWeight`,`Weight`,`MaxWeight`,`SoundFileLoc`,`ImageFileLoc`,`Allergy`,`PrimeItem`) VALUES ('3','Yogurt','205','35','50','65','','','Warning Contains Dairy','0');
INSERT INTO `Items` (`Barcode`,`Name`,`Price`,`MinWeight`,`Weight`,`MaxWeight`,`SoundFileLoc`,`ImageFileLoc`,`Allergy`,`PrimeItem`) VALUES ('5','Pasta','225','450','500','550','','','','1');
INSERT INTO `Items` (`Barcode`,`Name`,`Price`,`MinWeight`,`Weight`,`MaxWeight`,`SoundFileLoc`,`ImageFileLoc`,`Allergy`,`PrimeItem`) VALUES ('4','Long Grain Rice','250','375','400','425','','','','1');
INSERT INTO `Items` (`Barcode`,`Name`,`Price`,`MinWeight`,`Weight`,`MaxWeight`,`SoundFileLoc`,`ImageFileLoc`,`Allergy`,`PrimeItem`) VALUES ('6','Spaghetti','200','350','400','450','','','','1');
INSERT INTO `Items` (`Barcode`,`Name`,`Price`,`MinWeight`,`Weight`,`MaxWeight`,`SoundFileLoc`,`ImageFileLoc`,`Allergy`,`PrimeItem`) VALUES ('7','Basmati Rice','200','200','250','300','','','','1');
INSERT INTO `Items` (`Barcode`,`Name`,`Price`,`MinWeight`,`Weight`,`MaxWeight`,`SoundFileLoc`,`ImageFileLoc`,`Allergy`,`PrimeItem`) VALUES ('8','Beans','115','200','250','300','','','','1');
INSERT INTO `Items` (`Barcode`,`Name`,`Price`,`MinWeight`,`Weight`,`MaxWeight`,`SoundFileLoc`,`ImageFileLoc`,`Allergy`,`PrimeItem`) VALUES ('9','Spaghetti Hoops','119','100','125','150','','','','1');
INSERT INTO `Items` (`Barcode`,`Name`,`Price`,`MinWeight`,`Weight`,`MaxWeight`,`SoundFileLoc`,`ImageFileLoc`,`Allergy`,`PrimeItem`) VALUES ('10','Peas','100','50','75','100','','','','1');
INSERT INTO `Items` (`Barcode`,`Name`,`Price`,`MinWeight`,`Weight`,`MaxWeight`,`SoundFileLoc`,`ImageFileLoc`,`Allergy`,`PrimeItem`) VALUES ('11','Pasta Sauce','123','375','400','425','','','','1');
INSERT INTO `Items` (`Barcode`,`Name`,`Price`,`MinWeight`,`Weight`,`MaxWeight`,`SoundFileLoc`,`ImageFileLoc`,`Allergy`,`PrimeItem`) VALUES ('12','Bread','98','450','500','550','','','','1');


# Dump of table Recipes
# ------------------------------------------------------------

CREATE TABLE `Recipes` (
  `Name` tinytext,
  `PrimeItemBC` text,
  `OtherIngredients` text,
  `Instructions` text
) ENGINE=MyISAM DEFAULT CHARSET=utf8;

INSERT INTO `Recipes` (`Name`,`PrimeItemBC`,`OtherIngredients`,`Instructions`) VALUES ('Spaghetti Bolognese','5\n','Pasta Sauce, Minced Beef','Get a medium pan with small amount of olive oil, put the pan on medium heat. Add the meat, stirring and breaking up the meat with a wooden spoon. When cooked add sauce. Leave for 30-40 mins on low heat. Cook pasta in lots of boiling water with small pinch of salt.\n');
INSERT INTO `Recipes` (`Name`,`PrimeItemBC`,`OtherIngredients`,`Instructions`) VALUES ('Chicken Curry','4','Curry Sauce, Chicken Fillets','Get a medium pan with small amount of olive oil, put the pan on medium heat. Cut the fillets up into small pieces and add to pan. When cooked through add the sauce. Leave to simmer for about 15mins on low heat. Cook rice in boiling water until ready.\n');
INSERT INTO `Recipes` (`Name`,`PrimeItemBC`,`OtherIngredients`,`Instructions`) VALUES ('Beans on Toast','8','Bread, Butter','Put bread in toaster. Place beans into a microwave dish and put microwave for two mins. Butter the toast when ready. Take beans out of microwave and serve.');
INSERT INTO `Recipes` (`Name`,`PrimeItemBC`,`OtherIngredients`,`Instructions`) VALUES ('Spaghetti Bolognese','6','Pasta Sauce, Minced Beef','Get a medium pan with small amount of olive oil, put the pan on medium heat. Add the meat, stirring and breaking up the meat with a wooden spoon. When cooked add sauce. Leave for 30-40 mins on low heat. Cook pasta in lots of boiling water with small pinch of salt.\n');
INSERT INTO `Recipes` (`Name`,`PrimeItemBC`,`OtherIngredients`,`Instructions`) VALUES ('Lamb Curry','7','Curry Sauce, Diced Lamb','Get a medium pan with small amount of olive oil, put the pan on medium heat. When ready add diced lamb to pan. When cooked through add the sauce. Leave to simmer for about 15mins on low heat. Cook rice in boiling water until ready.\n');
INSERT INTO `Recipes` (`Name`,`PrimeItemBC`,`OtherIngredients`,`Instructions`) VALUES ('Spaghetti Hoops on Toast','9','Bread, Butter','Put bread in toaster. Place spaghetti hoops in a microwave dish into microwave for two mins. Butter the toast when ready. Take beans out of microwave and serve.');
INSERT INTO `Recipes` (`Name`,`PrimeItemBC`,`OtherIngredients`,`Instructions`) VALUES ('Peas with Noodles','10','Noodles, Cream, Salt\n','Put the peas to cook in boiling water, enough to cover. Add salt to taste. Let them cook gently until tender. Put the cream into a small fry pan, and stir over the fire until the oil separates from the albumen. As soon as the albumen turns a light brown, add to the stewed peas and boil up. Add the potato water and when boiling hot, sprinkle in the noodles. Let boil 15 or 20 minutes and serve. ');


# Dump of table Reminder
# ------------------------------------------------------------

CREATE TABLE `Reminder` (
  `CustomerID` int(11) NOT NULL,
  `Item1BC` tinytext,
  `Item2BC` tinytext,
  `Item3BC` tinytext,
  `Item4BC` tinytext,
  `Item5BC` tinytext,
  `Item6BC` tinytext,
  `Item7BC` tinytext,
  `Item8BC` tinytext,
  `Item9BC` tinytext,
  `Item10BC` tinytext,
  PRIMARY KEY  (`CustomerID`)
) ENGINE=MyISAM DEFAULT CHARSET=utf8;

INSERT INTO `Reminder` (`CustomerID`,`Item1BC`,`Item2BC`,`Item3BC`,`Item4BC`,`Item5BC`,`Item6BC`,`Item7BC`,`Item8BC`,`Item9BC`,`Item10BC`) VALUES ('5','test','test','test','test','test',NULL,NULL,NULL,NULL,NULL);
INSERT INTO `Reminder` (`CustomerID`,`Item1BC`,`Item2BC`,`Item3BC`,`Item4BC`,`Item5BC`,`Item6BC`,`Item7BC`,`Item8BC`,`Item9BC`,`Item10BC`) VALUES ('3','i like','food',NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);


# Dump of table Transactions
# ------------------------------------------------------------

CREATE TABLE `Transactions` (
  `TransactionID` bigint(20) NOT NULL default '0',
  PRIMARY KEY  (`TransactionID`)
) ENGINE=MyISAM DEFAULT CHARSET=utf8;



