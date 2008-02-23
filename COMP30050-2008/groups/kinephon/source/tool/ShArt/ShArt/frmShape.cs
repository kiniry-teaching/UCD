using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;

namespace ShArt
{
	public partial class frmShape: Form
	{

		protected Shape _shape;

		public frmShape()
		{
			InitializeComponent();
		}

		public Shape Shape
		{
			get { return _shape; }
			set
			{
				_shape = value;
				_shape.Form = this;
				Text = _shape.Name;
				picShape.Invalidate();
			}
		}

		private void picShape_Paint(object sender, PaintEventArgs e)
		{
			Pen grid = new Pen(Color.DarkGray);
			Pen box = new Pen(Color.Black);
			float w = picShape.ClientSize.Width;
			float h = picShape.ClientSize.Height;
			float dy = (h - 1) / _shape.Height;
			float dx = (w - 1) / _shape.Width;

			for(float x = 0; x < w; x += dx)
				e.Graphics.DrawLine(grid, x, 0, x, h);
		
			for(float y = 0; y < h; y += dy)
				e.Graphics.DrawLine(grid, 0, y, w, y);

			e.Graphics.DrawRectangle(box, dx * 4, dy * 4, dx * (_shape.Width - 8), dy * (_shape.Height - 8));

		}

		private void gridXToolStripMenuItem_Click(object sender, EventArgs e)
		{

		}

		private void Shape_Load(object sender, EventArgs e)
		{

		}

		private void frmShape_FormClosed(object sender, FormClosedEventArgs e)
		{
			if(WindowState == FormWindowState.Normal)
				_shape.WindowPosition = Bounds;
			_shape.Form = null;
		}
	}
}