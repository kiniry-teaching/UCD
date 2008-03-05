using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.IO;

namespace ShArt
{
	public partial class frmShArt: Form
	{

		protected string _projname;

		public frmShArt()
		{
			KBHook.OnKeydown += OnKeydown;
			InitializeComponent();
		}

		public void OnKeydown(Keys key)
		{
			stsStatus.Text = key.ToString();
			switch(key)
			{

				case Keys.OemMinus:
				case Keys.Oemplus:
					OnKeydownShape(key);
					break;


			}
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
			}

		}

		private void setCaption()
		{
			Text = "ShArt (v0.1) - [" + _projname + "]";
		}

		private void ShArt_Resize(object sender, EventArgs e)
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

		private void ShArt_Load(object sender, EventArgs e)
		{
			ShArt_Resize(null, null);
		}

		private void ShArt_MdiChildActivate(object sender, EventArgs e)
		{
			ToolStripManager.RevertMerge(tbrShArt);
			if(ActiveMdiChild != null)
			{	ToolStripManager.Merge(((frmShape)ActiveMdiChild).tbrShape, tbrShArt);
				tbrShArt.Visible = true;
				SelectShape(((frmShape)ActiveMdiChild).Shape.Node);
			}
			else
				tbrShArt.Visible = false;
			ShArt_Resize(null, null);
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
			zc = int.Parse(stream.ReadLine());
			cc = int.Parse(stream.ReadLine());

			for(int y = 0; y < shape.Height; y++)
			for(int x = 0; x < shape.Width; x++)
			{	shape.Pixels[x, y].Weight = float.Parse(stream.ReadLine());
				shape.Pixels[x, y].Radius = float.Parse(stream.ReadLine());
				shape.Pixels[x, y].Falloff = float.Parse(stream.ReadLine());
			}
			
			for(int zi = 0; zi < zc; zi++)
			{
				Zone zone = new Zone();
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

			if(_projname == null)
				rename = true;

			if(rename == true)
				if(dlgSave.ShowDialog() == DialogResult.Cancel)
					return false;

			_projname = dlgSave.FileName;
			setCaption();

			StreamWriter stream = new StreamWriter(File.Open(_projname, FileMode.Create, FileAccess.Write, FileShare.Read));

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
			stream.WriteLine(shape.Zones.Count);
			stream.WriteLine(shape.Node.Nodes.Count);

			// Pixel
			for(int y = 0; y < shape.Height; y++)
			for(int x = 0; x < shape.Width; x++)
			{	stream.WriteLine(shape.Pixels[x, y].Weight);
				stream.WriteLine(shape.Pixels[x, y].Radius);
				stream.WriteLine(shape.Pixels[x, y].Falloff);
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

		}

		private void frmShArt_FormClosing(object sender, FormClosingEventArgs e)
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

	}
}
