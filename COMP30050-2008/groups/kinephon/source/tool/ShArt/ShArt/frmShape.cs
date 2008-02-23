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
			float we;
			int r = 0, g = 0;

			for(int y = 0; y < _shape.Height; y++)
			for(int x = 0; x < _shape.Width; x++)
			{
				we = CalculateWeight(_shape.Pixels[x, y]);
				if(we < -1) we = -1;
				if(we >  1) we = 1;
				if(we < 0)
					r = (int)(62 * (-we));
				else
					g = (int)(62 * we);
				Brush b = new SolidBrush(Color.FromArgb(193 + r, 193 + g, 193));
				e.Graphics.FillRectangle(b, x * dx, y * dy, dx, dy);
			}

			for(float x = 0; x < w; x += dx)
				e.Graphics.DrawLine(grid, x, 0, x, h);
		
			for(float y = 0; y < h; y += dy)
				e.Graphics.DrawLine(grid, 0, y, w, y);

			e.Graphics.DrawRectangle(box, dx * 4, dy * 4, dx * (_shape.Width - 8), dy * (_shape.Height - 8));

		}

		private float CalculateWeight(Pixel pixel)
		{

			float w = pixel.Weight;

			foreach(Pixel p in pixel.Neighbours)
			{



			}

			return w;

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

		private void picShape_MouseDown(object sender, MouseEventArgs e)
		{

			if(e.Button == MouseButtons.Left || e.Button == MouseButtons.Right)
			{

				float w = picShape.ClientSize.Width;
				float h = picShape.ClientSize.Height;
				float dy = (h - 1) / _shape.Height;
				float dx = (w - 1) / _shape.Width;
				int x = (int)(e.X / dx);
				int y = (int)(e.Y / dy);
				if(e.Button == MouseButtons.Left)
					SetPixel(x, y, 8.0f, 1.0f, 0.0f);
				else
					SetPixel(x, y, 8.0f, 0.0f, 0.0f);
				picShape.Invalidate();

			}

		}

		private void picShape_MouseMove(object sender, MouseEventArgs e)
		{
			if(e.Button != MouseButtons.None)
				picShape_MouseDown(sender, e);
		}

		// x, y, radius, weight, falloff
		private void SetPixel(int cx, int cy, float r, float w, float f)
		{
			_shape.Pixels[cx, cy].Radius = r;
			_shape.Pixels[cx, cy].Weight = w;
			_shape.Pixels[cx, cy].Falloff = f;
			for(int y = cy - (int)Math.Floor(r); y < cy + (int)Math.Ceiling(r); y++)
			for(int x = cx - (int)Math.Floor(r); x < cx + (int)Math.Ceiling(r); x++)
				if(x != cx && y != cy)
					SetPixel(x, y, _shape.Pixels[cx, cy]);

		}

		private void SetPixel(int x, int y, Pixel n)
		{
			if(x >= 0 && y >= 0 && x < _shape.Width && y < _shape.Height)
				if(_shape.Pixels[x, y].Neighbours.Contains(n) == false)
					_shape.Pixels[x, y].Neighbours.Add(n);
		}

	}
}