<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.1//EN" "http://www.w3.org/TR/xhtml11/DTD/xhtml11.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">

<head>
<meta http-equiv="Content-Type" content="text/html; charset=utf-8" />
<title>Installation</title>
<style type="text/css">
	form{
		width:18em;
		font-family:"Times New Roman", Times, serif;
	}
	
	.formrow{
		width:18em;
		margin-bottom:2px;
	}
	
	.formtext{
		width:9em;
		display:inline-block;
	}
	
	.forminput{
		width:9em;
		display:inline-block;
	}
	
	.formbutton{
		width:9em;
	}
</style>
</head>

<body>
	<h1>Installation</h1>
	<ol>
		<li>Create a database on your server.</li>
		<li>Sign-up to <a href="http://www.amazon.com/AWS-home-page-Money/b/ref=gw_br_websvcs?ie=UTF8&node=3435361&pf_rd_p=369983801&pf_rd_s=left-nav-3&pf_rd_t=101&pf_rd_i=507846&pf_rd_m=ATVPDKIKX0DER&pf_rd_r=099VR55BA6VV8YDQ80DX">Amazon Web Services</a> and <a href="http://isbndb.com/">isbndb.com</a> to get your access keys.</li>
		<li>Enter the below details.</li>
		<li>Click submit and wait for welcome message.</li>
		<li>Then delete the "/install" folder to prevent anyone overwriting your installation.</li>
		<li>To access the administration functions intially, a user must register as ADMIN (all upper case)</li>
	</ol>
	<h2>Note:</h2>
	<ul>
		<li>There's a good chance you won't have to change "localhost".</li>
		<li>Username and password may be optional.</li>
		<li>For further information contact your host.</li>
	</ul>
	<?php
		if($_POST["dbname"] != NULL){
			include("install_functions.php");
			install($_POST["host"], $_POST["username"], $_POST["password"], $_POST["dbname"], $_POST["awskey"], $_POST["isbndbkey"]);	
		}
		else{
	?>
		<form action="index.php" method="post">
			<div class="formrow"><div class="formtext">Host: </div><div class="forminput"><input type="text" name="host" value="localhost" /></div></div>
			<div class="formrow"><div class="formtext">Database Username: </div><div class="forminput"><input type="text" name="username" /></div></div>
			<div class="formrow"><div class="formtext">Database Password: </div><div class="forminput"><input type="password" name="password" /></div></div>
			<div class="formrow"><div class="formtext">Database Name: </div><div class="forminput"><input type="text" name="dbname" /></div></div>
			<div class="formrow"><div class="formtext">AWS Access Key: </div><div class="forminput"><input type="text" name="awskey" /></div></div>
			<div class="formrow"><div class="formtext">isbndb.com Access Key: </div><div class="forminput"><input type="text" name="isbndbkey" /></div></div>
			<div class="formbutton"><input type="submit" /></div>
		</form>
	<?php
		}
	?>
	<?php //TODO - Thomas - Add user-system install process ?>
</body>

</html>