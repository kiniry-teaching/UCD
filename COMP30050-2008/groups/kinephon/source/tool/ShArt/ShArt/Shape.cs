using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;

namespace ShArt
{
	public partial class Shape: Form
	{
		public Shape()
		{
			InitializeComponent();
		}

		private void picShape_Paint(object sender, PaintEventArgs e)
		{
			Pen grid = new Pen(Color.DarkGray);
			Pen box = new Pen(Color.Black);
			float w = picShape.ClientSize.Width;
			float h = picShape.ClientSize.Height;
			float dy = (h - 1) / 32;
			float dx = (w - 1) / 32;

			for(float x = 0; x < w; x += dx)
				e.Graphics.DrawLine(grid, x, 0, x, h);
		
			for(float y = 0; y < h; y += dy)
				e.Graphics.DrawLine(grid, 0, y, w, y);

			e.Graphics.DrawRectangle(box, dx * 4, dy * 4, dx * 24, dy * 24);

		}
	}
}