<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.1//EN" "http://www.w3.org/TR/xhtml11/DTD/xhtml11.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">

<head>
<meta content="text/html; charset=utf-8" http-equiv="Content-Type" />
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
		<li>Sign-up to <a href="http://www.amazon.com/AWS-home-page-Money/b/ref=gw_br_websvcs?ie=UTF8&amp;node=3435361&amp;pf_rd_p=369983801&amp;pf_rd_s=left-nav-3&amp;pf_rd_t=101&amp;pf_rd_i=507846&amp;pf_rd_m=ATVPDKIKX0DER&amp;pf_rd_r=099VR55BA6VV8YDQ80DX">Amazon Web Services</a> and <a href="http://isbndb.com/">isbndb.com</a> to get your access keys.</li>
		<li>Enter the below details.</li>
		<li>Click submit and wait for welcome message.</li>
		<li>Then delete the &quot;/install&quot; folder to prevent anyone overwriting your installation.</li>
		<li>To access the administration functions intially, a user must register as admin (all lower case)</li>
	</ol>
	<h2>Note:</h2>
	<ul>
		<li>There&#39;s a good chance you won&#39;t have to change &quot;localhost&quot;.</li>
		<li>Username and password may be optional.</li>
		<li>For further information contact your host.</li>
		<li>&quot;Full path&quot; means the full path to your Alexandria installation (eg. <?php echo $_SERVER['DOCUMENT_ROOT'];?>/library)</li>
	</ul>
	<?php
		if($_POST["dbname"] != NULL){
			include("install_functions.php");
			install($_POST["host"], $_POST["username"], $_POST["password"], $_POST["dbname"], $_POST["awskey"], $_POST["isbndbkey"], $_POST['address']);	
		}
		else{
	?>
		<form action="index.php" method="post">
			<div class="formrow"><div class="formtext">Host: </div><div class="forminput"><input name="host" type="text" value="localhost" /></div></div>
			<div class="formrow"><div class="formtext">Database Username: </div><div class="forminput"><input name="username" type="text" /></div></div>
			<div class="formrow"><div class="formtext">Database Password: </div><div class="forminput"><input name="password" type="password" /></div></div>
			<div class="formrow"><div class="formtext">Database Name: </div><div class="forminput"><input name="dbname" type="text" /></div></div>
			<div class="formrow"><div class="formtext">AWS Access Key: </div><div class="forminput"><input name="awskey" type="text" /></div></div>
			<div class="formrow"><div class="formtext">isbndb.com Access Key: </div><div class="forminput"><input name="isbndbkey" type="text" /></div></div>
			<div class="formrow"><div class="formtext">Full path: </div><div class="forminput"><input name="address" type="text" value="<?php echo $_SERVER['DOCUMENT_ROOT'];?>" /></div></div>
			<div class="formbutton"><input type="submit" /></div>
		</form>
	<?php
		}
	?>
	<?php //TODO - Thomas - Add user-system install process ?>
</body>

</html>