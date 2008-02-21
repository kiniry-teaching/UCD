using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;

namespace ShArt
{
	public partial class ShArt: Form
	{
		public ShArt()
		{
			InitializeComponent();
		}

		private void testToolStripMenuItem_Click(object sender, EventArgs e)
		{
			Shape s = new Shape();
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
			{	ToolStripManager.Merge(((Shape)ActiveMdiChild).tbrShape, tbrShArt);
				tbrShArt.Visible = true;
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

		private void mnuWindowWindows_Click(object sender, EventArgs e)
		{
			
		}

	}
}
