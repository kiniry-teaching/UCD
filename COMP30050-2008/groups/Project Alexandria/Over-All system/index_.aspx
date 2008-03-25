<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">

<head>
<meta http-equiv="Content-Language" content="en-ie" />
<meta http-equiv="Content-Type" content="text/html; charset=utf-8" />
<title>Home Page</title>
<style type="text/css">
.style1 {
	border: 3px solid #000000;
}
.style2 {
	text-align: center;
	font-size: medium;
}
.style3 {
	border: 2px solid #000000;
}
</style>
</head>

<body style="margin: 0; background-color: #FFFFFF;">

<form id="form1" runat="server">
	<div style="position: absolute; width: 333px; height: 114px; z-index: 2; left: 22px; top: 21px; font-weight: bold; color: #000080;" id="layer2">
		&nbsp;&nbsp; BOOK SEARCH OPTIONS
		<br />
		..................................................................................<br />
		<asp:TextBox runat="server" id="TextBox1" Width="114px" BorderColor="White" BorderWidth="2px" Height="22px" BorderStyle="Groove">
		</asp:TextBox>
&nbsp;<asp:Button runat="server" Text="Search" id="Button1" BorderColor="Black" BorderStyle="Groove" ForeColor="Navy" /><br />
		<select name="Select1" style="width: 117px">
		<option></option>
		<option>ISBN</option>
		<option>AUTHOR</option>
		<option>TITLE</option>
		</select><br />
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;
	</div>
	<div style="position: absolute; height: 125px; z-index: 3; left: 14px; top: 15px; width: 352px" id="layer3">
		<table style="width: 100%; height: 124px" class="style1">
			<tr>
				<td style="height: 21px"></td>
			</tr>
		</table>
	</div>
</form>

<div style="position: absolute; width: 834px; height: 175px; z-index: 4; left: 18px; top: 219px; color: #000080; font-size: medium; font-weight: bold; text-decoration: blink;" id="layer4" class="style2">
	RECENTLY ADDED BOOKS<br />
	<table style="width: 100%" class="style1">
		<tr>
			<td class="style3">&nbsp;</td>
			<td class="style3">&nbsp;</td>
			<td>&nbsp;</td>
		</tr>
		<tr>
			<td class="style3">&nbsp;</td>
			<td class="style3">&nbsp;</td>
			<td>&nbsp;</td>
		</tr>
		<tr>
			<td class="style3">&nbsp;</td>
			<td class="style3">&nbsp;</td>
			<td>&nbsp;</td>
		</tr>
		<tr>
			<td class="style3">&nbsp;</td>
			<td class="style3">&nbsp;</td>
			<td>&nbsp;</td>
		</tr>
		<tr>
			<td class="style3">&nbsp;</td>
			<td>&nbsp;</td>
			<td>&nbsp;</td>
		</tr>
		<tr>
			<td class="style3">&nbsp;</td>
			<td>&nbsp;</td>
			<td>&nbsp;</td>
		</tr>
	</table>
</div>

</body>

</html>
