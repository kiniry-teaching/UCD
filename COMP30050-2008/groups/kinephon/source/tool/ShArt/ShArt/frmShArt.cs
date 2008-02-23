using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;

namespace ShArt
{
	public partial class frmShArt: Form
	{
		public frmShArt()
		{
			InitializeComponent();
		}

		private void testToolStripMenuItem_Click(object sender, EventArgs e)
		{
			frmShape s = new frmShape();
			s.MdiParent = this;
			s.Show();
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

			Shape shape = new Shape(tvwShapes.Nodes[0].Nodes.Add("New Shape"));
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

		private Shape Shape(TreeNode Node)
		{
			return (Shape)Node.Tag;
		}

		private void tvwShapes_AfterSelect(object sender, TreeViewEventArgs e)
		{
			if(e.Node.ImageIndex == 1)
			{	Shape shape = Shape(e.Node);
				pgdProperties.SelectedObject = shape;
				if(shape.Form != null)
					shape.Form.Activate();
			}
			else
				pgdProperties.SelectedObject = null;
		}

		private void tvwShapes_MouseDoubleClick(object sender, MouseEventArgs e)
		{
			if(tvwShapes.SelectedNode.ImageIndex == 1)
			{
				Shape shape = Shape(tvwShapes.SelectedNode);
				if(shape.Form != null)
					shape.Form.Activate();
				else
					ShowShape(shape);
			}
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

	}
}
