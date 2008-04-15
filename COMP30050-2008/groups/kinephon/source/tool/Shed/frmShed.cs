using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.IO;

namespace Shed
{
	public partial class frmShed: Form
	{

		protected string _projname;
		protected string _compname;

		public frmShed()
		{
			KBHook.OnKeydown += OnKeydown;
			InitializeComponent();
		}

		public void OnKeydown(Keys key)
		{
			stsStatus.Text = key.ToString();
			OnKeydownShape(key);
		}

		public void OnKeydownShape(Keys key)
		{
			frmShape shape;

			if(ActiveMdiChild is frmShape)
				shape = (frmShape)ActiveMdiChild;
			else
				return;

			switch(key)
			{
				case Keys.OemMinus: shape.mnuImageWeightDec_Click(null, null); break;
				case Keys.Oemplus: shape.mnuImageWeightInc_Click(null, null); break;
				case Keys.OemOpenBrackets: shape.mnuImageRadiusDec_Click(null, null); break;
				case Keys.Oem6: shape.mnuImageRadiusInc_Click(null, null); break;
				//case Keys.Oemtilde: shape.mnuImageFalloffDec_Click(null, null); break;
				//case Keys.Oem7: shape.mnuImageRadiusInc_Click(null, null); break;
				case Keys.P: shape.mnuImagePaint_Click(null, null); break;
				case Keys.A: shape.mnuZoneAdd_Click(null, null); break;
				case Keys.G:
					shape.mnuViewGrid.Checked = !shape.mnuViewGrid.Checked;
					shape.mnuViewGrid_Click(null, null); break;
				case Keys.L:
					shape.mnuViewGlow.Checked = !shape.mnuViewGlow.Checked;
					shape.mnuViewGlow_Click(null, null); break;
				case Keys.Z:
					shape.mnuViewZone_Click(null, null); break;
				case Keys.N:
					shape.mnuViewNegative.Checked = !shape.mnuViewNegative.Checked;
					shape.mnuViewNegative_Click(null, null); break;
				case Keys.X: shape.mnuView1to1_Click(null, null); break;
				case Keys.Q: shape.mnuImageWeight0_Click(null, null); break;
				case Keys.W: shape.mnuImageWeight1_Click(null, null); break;
				case Keys.E: shape.mnuImageWeight2_Click(null, null); break;
				case Keys.R: shape.mnuImageWeight3_Click(null, null); break;
				case Keys.T: shape.mnuImageWeight4_Click(null, null); break;
				case Keys.D1: shape.mnuImageRadius01_Click(null, null); break;
				case Keys.D2: shape.mnuImageRadius02_Click(null, null); break;
				case Keys.D3: shape.mnuImageRadius03_Click(null, null); break;
				case Keys.D4: shape.mnuImageRadius04_Click(null, null); break;
				case Keys.D5: shape.mnuImageRadius05_Click(null, null); break;
				case Keys.D6: shape.mnuImageRadius10_Click(null, null); break;
				case Keys.D7: shape.mnuImageRadius15_Click(null, null); break;
				case Keys.D8: shape.mnuImageRadius20_Click(null, null); break;
				case Keys.D9: shape.mnuImageRadius50_Click(null, null); break;
			}

		}

		private void setCaption()
		{
			Text = "Shed (v0.1) - [" + _projname + "]";
		}

		private void Shed_Resize(object sender, EventArgs e)
		{
			splPropertiesSplit_SplitterMoved(null, null);
			spcProperties.Height = splPropertiesSplit.ClientSize.Height;
		}

		private void splPropertiesSplit_SplitterMoved(object sender, SplitterEventArgs e)
		{
			spcProperties.Top = splProperties.Top;
			spcProperties.Width = splProperties.ClientSize.Width - 1;
			spcProperties.Left = ClientRectangle.Width - spcProperties.Width;
		}

		private void spcProperties_Panel2_Resize(object sender, EventArgs e)
		{
			pgdProperties.Width = spcProperties.Panel2.ClientSize.Width;
			pgdProperties.Height = spcProperties.Panel2.ClientSize.Height;
		}

		private void Shed_Load(object sender, EventArgs e)
		{
			Shed_Resize(null, null);
		}

		private void Shed_MdiChildActivate(object sender, EventArgs e)
		{
			ToolStripManager.RevertMerge(tbrShed);
			if(ActiveMdiChild != null)
			{	ToolStripManager.Merge(((frmShape)ActiveMdiChild).tbrShape, tbrShed);
				tbrShed.Visible = true;
				SelectShape(((frmShape)ActiveMdiChild).Shape.Node);
			}
			else
				tbrShed.Visible = false;
			Shed_Resize(null, null);
		}

		private void exitToolStripMenuItem_Click(object sender, EventArgs e)
		{
			Close();
		}

		private void mnuWindowArrange_Click(object sender, EventArgs e)
		{
			LayoutMdi(MdiLayout.ArrangeIcons);
		}

		private void mnuWindowCascade_Click(object sender, EventArgs e)
		{
			LayoutMdi(MdiLayout.Cascade);
		}

		private void mnuWindowHorizontal_Click(object sender, EventArgs e)
		{
			LayoutMdi(MdiLayout.TileHorizontal);
		}

		private void mnuWindowVertical_Click(object sender, EventArgs e)
		{
			LayoutMdi(MdiLayout.TileVertical);
		}

		private void mnuWindowCloseAll_Click(object sender, EventArgs e)
		{
			foreach(Form form in MdiChildren)
				form.Close();
		}

		private void mnuShapeNew_Click(object sender, EventArgs e)
		{
			if(tvwShapes.Nodes.Count == 0)
				tvwShapes.Nodes.Add("Shapes");

			Shape shape = new Shape(tvwShapes.Nodes[0].Nodes.Add("SID_*"));
			shape.Node.SelectedImageIndex = shape.Node.ImageIndex = 1;

			ShowShape(shape);
			SelectShape(shape.Node);

		}

		public void SelectShape(TreeNode node)
		{

			node.EnsureVisible();
			tvwShapes.SelectedNode = node;

		}

		public void SelectPixel(Pixel pixel)
		{
			pgdProperties.SelectedObject = pixel;
		}

		public Shape Shape(TreeNode Node)
		{
			return (Shape)Node.Tag;
		}

		private void tvwShapes_AfterSelect(object sender, TreeViewEventArgs e)
		{
			if(e.Node.Tag is Shape)
			{	Shape shape = Shape(e.Node);
				pgdProperties.SelectedObject = shape;
				if(shape.Form != null)
					shape.Form.Activate();
			}
			else
				pgdProperties.SelectedObject = null;

			if(e.Node.Parent != null && e.Node.Parent.Parent == null)
				if(Shape(e.Node).Type == TypesOfShape.Movement)
					mnuShapeNewChild.Enabled = true;
				else
					mnuShapeNewChild.Enabled = false;
			else
				mnuShapeNewChild.Enabled = true;

		}

		private void tvwShapes_MouseDoubleClick(object sender, MouseEventArgs e)
		{
			if(tvwShapes.SelectedNode.Tag is Shape)
			{
				Shape shape = Shape(tvwShapes.SelectedNode);
				if(shape.Form != null)
					shape.Form.Activate();
				else
					ShowShape(shape);
			}
			if(tvwShapes.SelectedNode.IsExpanded == false)
				tvwShapes.SelectedNode.Expand();
		}

		private void ShowShape(Shape shape)
		{
			frmShape frmShape = new frmShape();
			frmShape.MdiParent = this;
			frmShape.Shape = shape;
			if(shape.WindowPosition != null)
				frmShape.Bounds = shape.WindowPosition;
			frmShape.Show();
		}

		private void mnuShapeNewChild_Click(object sender, EventArgs e)
		{
			TreeNode node = tvwShapes.SelectedNode;

			if(node.Parent != null && node.Parent.Parent != null)
				node = node.Parent;

			if(node.ImageIndex == 1)
			{

				Shape shape = new Shape(node.Nodes.Add("SID_*"));
				shape.Node.SelectedImageIndex = shape.Node.ImageIndex = 2;
				shape.Type = TypesOfShape.Speed;

				ShowShape(shape);
				SelectShape(shape.Node);

			}

		}

		private void mnuFileOpen_Click(object sender, EventArgs e)
		{
			Open();
		}

		private void mnuFileSave_Click(object sender, EventArgs e)
		{
			Save(false);
		}

		private void mnuFileSaveAs_Click(object sender, EventArgs e)
		{
			Save(true);
		}

		private void Open()
		{
			TreeNode rootnode;

			if(dlgOpen.ShowDialog() == DialogResult.Cancel)
				return;

			tvwShapes.Nodes.Clear();
			rootnode = tvwShapes.Nodes.Add("Shapes");

			_projname = dlgOpen.FileName;
			setCaption();

			StreamReader stream = new StreamReader(File.Open(_projname, FileMode.Open, FileAccess.Read, FileShare.Read));

			_compname = stream.ReadLine();
			int nc = int.Parse(stream.ReadLine());

			for(int i = 0; i < nc; i++)
				Open(stream, rootnode);

			stream.Close();

		}

		private void Open(StreamReader stream, TreeNode parentNode)
		{
			int zc;
			int cc;

			Shape shape = new Shape(parentNode.Nodes.Add(stream.ReadLine()));
			shape.Node.SelectedImageIndex = shape.Node.ImageIndex = 1;
			shape.Node.EnsureVisible();

			shape.SID = uint.Parse(stream.ReadLine());
			shape.Type = (TypesOfShape)(int.Parse(stream.ReadLine()));
			shape.Dampen = float.Parse(stream.ReadLine());
			shape.Width = int.Parse(stream.ReadLine());
			shape.Height = int.Parse(stream.ReadLine());
			shape.HBound = int.Parse(stream.ReadLine());
			shape.VBound = int.Parse(stream.ReadLine());
			shape.WindowPosition = new Rectangle
			(	int.Parse(stream.ReadLine()),
				int.Parse(stream.ReadLine()),
				int.Parse(stream.ReadLine()),
				int.Parse(stream.ReadLine())
			);
			shape.ZoneReverse = bool.Parse(stream.ReadLine());
			shape.ZoneAnyStart = bool.Parse(stream.ReadLine());
			zc = int.Parse(stream.ReadLine());
			cc = int.Parse(stream.ReadLine());

			for(int y = 0; y < shape.Height; y++)
			for(int x = 0; x < shape.Width; x++)
			{	shape.Pixels.Pixel[x, y].Weight = float.Parse(stream.ReadLine());
				shape.Pixels.Pixel[x, y].Radius = float.Parse(stream.ReadLine());
				shape.Pixels.Pixel[x, y].Falloff = float.Parse(stream.ReadLine());
			}
			
			for(int zi = 0; zi < zc; zi++)
			{
				Zone zone = new Zone(shape);
				zone.X = float.Parse(stream.ReadLine());
				zone.Y = float.Parse(stream.ReadLine());
				zone.EnterRadius = float.Parse(stream.ReadLine());
				zone.ExitRadius = float.Parse(stream.ReadLine());
				zone.EnterAngle = float.Parse(stream.ReadLine());
				zone.ExitAngle = float.Parse(stream.ReadLine());
				zone.EnterArc = float.Parse(stream.ReadLine());
				zone.ExitArc = float.Parse(stream.ReadLine());
				shape.Zones.Add(zone);
			}

			for(int ci = 0; ci < cc; ci++)
				Open(stream, shape.Node);

		}

		private bool Save(bool rename)
		{
			if(tvwShapes.Nodes.Count == 0)
				tvwShapes.Nodes.Add("Shapes");

			if(_projname == null || _projname == "")
				rename = true;

			if(rename == true)
				if(dlgSave.ShowDialog() == DialogResult.Cancel)
					return false;
				else
					_projname = dlgSave.FileName;
			setCaption();

			StreamWriter stream = new StreamWriter(File.Open(_projname, FileMode.Create, FileAccess.Write, FileShare.Read));

			stream.WriteLine(_compname);
			stream.WriteLine(tvwShapes.Nodes[0].Nodes.Count);

			foreach(TreeNode n in tvwShapes.Nodes[0].Nodes)
				if(Save(stream, n) == false)
					break;

			stream.Close();

			return true;

		}

		private bool Save(StreamWriter stream, TreeNode node)
		{
			if(!(node.Tag is Shape))
				return true;

			Shape shape = (Shape)node.Tag;

			// Header
			stream.WriteLine(shape.Name);
			stream.WriteLine(shape.SID);
			stream.WriteLine((int)shape.Type);
			stream.WriteLine(shape.Dampen);
			stream.WriteLine(shape.Width);
			stream.WriteLine(shape.Height);
			stream.WriteLine(shape.HBound);
			stream.WriteLine(shape.VBound);
			stream.WriteLine(shape.WindowPosition.X);
			stream.WriteLine(shape.WindowPosition.Y);
			stream.WriteLine(shape.WindowPosition.Width);
			stream.WriteLine(shape.WindowPosition.Height);
			stream.WriteLine(shape.ZoneReverse);
			stream.WriteLine(shape.ZoneAnyStart);
			stream.WriteLine(shape.Zones.Count);
			stream.WriteLine(shape.Node.Nodes.Count);

			// Pixel
			for(int y = 0; y < shape.Height; y++)
			for(int x = 0; x < shape.Width; x++)
			{	stream.WriteLine(shape.Pixels.Pixel[x, y].Weight);
				stream.WriteLine(shape.Pixels.Pixel[x, y].Radius);
				stream.WriteLine(shape.Pixels.Pixel[x, y].Falloff);
			}

			// Zones
			for(int i = 0; i < shape.Zones.Count; i++)
			{	stream.WriteLine(shape.Zones[i].X);
				stream.WriteLine(shape.Zones[i].Y);
				stream.WriteLine(shape.Zones[i].EnterRadius);
				stream.WriteLine(shape.Zones[i].ExitRadius);
				stream.WriteLine(shape.Zones[i].EnterAngle);
				stream.WriteLine(shape.Zones[i].ExitAngle);
				stream.WriteLine(shape.Zones[i].EnterArc);
				stream.WriteLine(shape.Zones[i].ExitArc);
			}

			foreach(TreeNode n in node.Nodes)
				if(Save(stream, n) == false)
					return false;

			return true;

		}

		private void mnuFileCompile_Click(object sender, EventArgs e)
		{
			Compile(false);
		}

		private void mnuFileCompileTo_Click(object sender, EventArgs e)
		{
			Compile(true);
		}

		private void Compile(bool rename)
		{
			if(tvwShapes.Nodes.Count == 0 || tvwShapes.Nodes[0].Nodes.Count == 0)
			{	MessageBox.Show("Nothing to compile");
				return;
			}

			if(_compname == null || _compname == "")
				rename = true;

			if(rename == true)
			{
				dlgCompile.SelectedPath = _compname;
				if(dlgCompile.ShowDialog() == DialogResult.Cancel)
					return;
				else
					_compname = dlgCompile.SelectedPath;
			}

			if(_compname[_compname.Length - 1] != '\\')
				_compname += "\\";

			CompileHFile();
			CompileKFile();

			MessageBox.Show("Compiled");

		}

		private void CompileHFile()
		{

			StreamWriter stream = new StreamWriter(_compname + "ShapeId.h");
			uint SID = 1;
			StringBuilder sb = new StringBuilder();

			stream.WriteLine("#ifndef __INTERPRETER_SHAPEID_H__");
			stream.WriteLine("#define __INTERPRETER_SHAPEID_H__");
			stream.WriteLine();
			stream.WriteLine("namespace interpreter");
			stream.WriteLine("{");
			stream.WriteLine();
			stream.WriteLine("/**");
			stream.WriteLine(" * List of all shapes by their id in the kinephon.sec shape file");
			stream.WriteLine(" * This header was generated by Shed");
			stream.WriteLine(" * @author EB");
			stream.WriteLine(" * @version 1.0");
			stream.WriteLine(" */");
			stream.WriteLine("namespace esid");
			stream.WriteLine("{");
			stream.WriteLine();

			CompileHFile(tvwShapes.Nodes[0].Nodes, sb, ref SID);
			CompileHFile(stream, sb);

			stream.WriteLine();
			stream.WriteLine("}");
			stream.WriteLine();
			stream.WriteLine("}");
			stream.WriteLine();
			stream.WriteLine("#endif");

			stream.Close();

		}

		private void CompileHFile(StreamWriter stream, StringBuilder sb)
		{
			StringReader reader = new StringReader(sb.ToString());
			int maxlen = 0;
			string line;

			while((line = reader.ReadLine()) != null)
			{
				if(line.Length > maxlen)
					maxlen = line.Length;
				reader.ReadLine();
			}

			maxlen = maxlen + 1;
			reader = new StringReader(sb.ToString());

			while((line = reader.ReadLine()) != null)
			{

				while(line.Length < maxlen)
					line += " ";

				stream.WriteLine(line + reader.ReadLine());

			}

		}

		private void CompileHFile(TreeNodeCollection nodes, StringBuilder sb, ref uint SID)
		{
			Shape shape;
			string UseName;
			string Comment;

			foreach(TreeNode node in nodes)
			{

				if(node.Tag is Shape)
				{

					shape = (Shape)node.Tag;

					if(shape.SID == 0)
					{	while(SIDUsed(SID, tvwShapes.Nodes[0]) == true)
							SID++;
						shape.UseSID = SID;
						SID++;
					}
					else
						shape.UseSID = shape.SID;
					
					UseName = shape.Name;
					if(UseName.IndexOf('*') != -1)
						UseName = UseName.Replace("*", shape.UseSID.ToString());

					Comment = "";

					if(node.Parent.Parent != null)
						Comment += "- ";

					if(shape.Type == TypesOfShape.Movement)
						Comment += "Movement";
					else
					if(shape.Type == TypesOfShape.Speed)
						Comment += "Speed";
					else
						Comment += "Accel";

					sb.AppendLine("\tsid const " + UseName);
					sb.AppendLine("= " + shape.UseSID + "; // " + Comment);

					CompileHFile(node.Nodes, sb, ref SID);

				}

			}

		}

		private bool SIDUsed(uint v, TreeNode node)
		{
			Shape shape;

			if(node.Tag is Shape)
			{
				shape = (Shape)node.Tag;
				if(shape.SID == v)
					return true;
			}

			foreach(TreeNode n in node.Nodes)
				if(SIDUsed(v, n) == true)
					return true;

			return false;

		}

		private void CompileKFile()
		{

			Stream s = new StreamWriter(_compname + "kinephon.sec").BaseStream;
			BinaryWriter stream = new BinaryWriter(s);
			stream.Write('S');
			stream.Write('E');
			stream.Write('V');
			stream.Write('1');
			stream.Write(tvwShapes.Nodes[0].Nodes.Count);
			CompileKFile(stream, tvwShapes.Nodes[0].Nodes, TypesOfShape.Movement);
			stream.Close();

		}

		private void CompileKFile(BinaryWriter stream, TreeNodeCollection nodes, TypesOfShape type)
		{	Shape shape;
			int speedShapes;
			int accelShapes;
			Shape cShape;

			foreach(TreeNode node in nodes)
			{

				if(!(node.Tag is Shape))
					continue;

				shape = (Shape)node.Tag;
				speedShapes = 0;
				accelShapes = 0;

				// If type is movement, any type will export
				//	otherwise, only export if the type specified
				//	is the type being tested now
				if(type != TypesOfShape.Movement)
					if(type != shape.Type)
						continue;

				foreach(TreeNode cnode in node.Nodes)
					if(cnode.Tag is Shape)
					{	cShape = (Shape)cnode.Tag;
						if(cShape.Type == TypesOfShape.Speed)
							speedShapes++;
						else
						if(cShape.Type == TypesOfShape.Acceleration)
							accelShapes++;
					}


				stream.Write((uint)shape.Type);
				stream.Write(shape.UseSID);
				stream.Write(shape.Width);
				stream.Write(shape.Width * shape.Height);
				stream.Write(shape.HBound);
				stream.Write(shape.VBound);
				stream.Write(shape.Zones.Count);
				stream.Write(speedShapes);
				stream.Write(accelShapes);
				stream.Write(shape.ZoneAnyStart);
				stream.Write(shape.ZoneReverse);
				stream.Write((byte)0);
				stream.Write((byte)0);

				CompileKFile(stream, shape.Zones);
				CompileKFile(stream, shape);

				// Export only speed shapes, followed by accel shapes
				//	(don't allow them to be interleaved)
				CompileKFile(stream, node.Nodes, TypesOfShape.Speed);
				CompileKFile(stream, node.Nodes, TypesOfShape.Acceleration);

			}

		}

		private void CompileKFile(BinaryWriter stream, Zones zones)
		{	float Angle;
			float Arc;

			foreach(Zone zone in zones)
			{

				stream.Write(zone.X);
				stream.Write(zone.Y);

				Angle = zone.EnterAngle;
				Arc = zone.EnterArc;
				if(Angle < 0) Angle += 360;
				if(Arc < 0) Arc = -Arc;
				Angle *= (float)(Math.PI / 180);
				Arc *= (float)(Math.PI / 180);

				stream.Write(zone.EnterRadius);
				stream.Write(Angle);
				stream.Write(Arc);

				Angle = zone.ExitAngle;
				Arc = zone.ExitArc;
				if(Angle < 0) Angle += 360;
				if(Arc < 0) Arc = -Arc;
				Angle *= (float)(Math.PI / 180);
				Arc *= (float)(Math.PI / 180);

				stream.Write(zone.ExitRadius);
				stream.Write(Angle);
				stream.Write(Arc);

			}

		}

		private void CompileKFile(BinaryWriter stream, Shape shape)
		{	float DimWeight;

			shape.Pixels.CalculateNeighbours();
			DimWeight = shape.CalculateDimmingWeight();

			for(int y = 0; y < shape.Height; y++)
			for(int x = 0; x < shape.Width; x++)
				stream.Write
				(	(byte)(shape.Pixels.Pixel[x, y].CalculateWeight
					(	DimWeight,
						0.0f,
						1.0f
					) * 255)
				);

		}

		private void frmShed_FormClosing(object sender, FormClosingEventArgs e)
		{
			switch(MessageBox.Show(this, "Save?", "Save?", MessageBoxButtons.YesNoCancel))
			{
				case DialogResult.Yes:
					if(Save(false) == false)
						e.Cancel = true;
					break;
				case DialogResult.No:
					break;
				case DialogResult.Cancel:
					e.Cancel = true;
					break;
			}
		}

		private void mnuShapeDelete_Click(object sender, EventArgs e)
		{
			tvwShapes.SelectedNode.Remove();
		}

		private void pgdProperties_PropertyValueChanged(object s, PropertyValueChangedEventArgs e)
		{
			frmShape shape;

			if(ActiveMdiChild is frmShape)
				shape = (frmShape)ActiveMdiChild;
			else
				return;

			shape.picShape.Invalidate();
//			pgdProperties.Refresh();

		}

	}
}
