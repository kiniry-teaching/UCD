using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.Threading;

namespace ShArt
{
	public enum TypesOfTool
	{
		Select,
		Paint,
		Draw,
		Line
	}

	public partial class frmShape: Form
	{

		protected Shape _shape;
		protected TypesOfTool _tool = TypesOfTool.Paint;
		protected float _radius = 5.0f;
		protected float _weight = 1.0f;
		protected float _falloff = 0.0f;

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
			int r = 0, g = 0, b = 0;
			float mwe = 1.0f;

			for(int y = 0; y < _shape.Height; y++)
			for(int x = 0; x < _shape.Width; x++)
			{
				if((we = CalculateWeight(_shape.Pixels[x, y])) > mwe)
					mwe = we;
			}

			for(int y = 0; y < _shape.Height; y++)
			for(int x = 0; x < _shape.Width; x++)
			{
				we = CalculateWeight(_shape.Pixels[x, y]) / mwe;
				if(we < -1) we = -1;
				if(we >  1) we = 1;
				if(we < 0)
					r = (int)(62 * (-we));
				else
					g = (int)(62 * we);
				if(_shape.Pixels[x, y].Weight > 0)
					b = 62;
				else
				if(_shape.Pixels[x, y].Weight < 0)
					b = -62;
				else
					b = 0;
				Brush br = new SolidBrush(Color.FromArgb(193 + r, 193 + g, 193 + b));
				e.Graphics.FillRectangle(br, x * dx, y * dy, dx, dy);
			}

			if(mnuViewGrid.Checked == true)
			{

				for(float x = 0; x < w; x += dx)
					e.Graphics.DrawLine(grid, x, 0, x, h);
			
				for(float y = 0; y < h; y += dy)
					e.Graphics.DrawLine(grid, 0, y, w, y);

				e.Graphics.DrawRectangle(box, dx * 4, dy * 4, dx * (_shape.Width - 8), dy * (_shape.Height - 8));

			}

		}

		private float CalculateWeight(Pixel p)
		{

			float d;
			float w = p.Weight;
			Pixel np;

			if(p.Neighbours != null && p.Neighbours.Count != 0)
				for(int i = 0; i < p.Neighbours.Count; i++)
				{

					np = p.Neighbours[i];

					d = Distance(p.X, p.Y, np.X, np.Y);

					if(d > np.Radius)
					{	// Too far away - don't consider this neighbour again
						p.Neighbours.Remove(np);
						i--;
					}
					else
						w += (1 - (d / np.Radius)) * np.Weight;

				}

			return w;

		}

		private float Distance(int x, int y, int u, int v)
		{

			int dx = u - x;
			int dy = v - y;

			return (float)Math.Sqrt(dx * dx + dy * dy);

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

				if(x < 0 || x >= _shape.Width || y < 0 || y >= _shape.Height)
					return;

				if(e.Button == MouseButtons.Left)
					SetPixel(x, y, _radius, 1.0f, 0.0f);
				else
					SetPixel(x, y, 1.0f, 0.0f, 0.0f);
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
				if(!(x == cx && y == cy))
					SetPixel(x, y, _shape.Pixels[cx, cy]);

		}

		private void SetPixel(int x, int y, Pixel n)
		{
			if(x >= 0 && y >= 0 && x < _shape.Width && y < _shape.Height)
				if(_shape.Pixels[x, y].Neighbours.Contains(n) == false)
					_shape.Pixels[x, y].Neighbours.Add(n);
		}

		private void mnuImageClear_Click(object sender, EventArgs e)
		{
			for(int y = 0; y < _shape.Height; y++)
			for(int x = 0; x < _shape.Width; x++)
				SetPixel(x, y, 1.0f, 0.0f, 0.0f);
			picShape.Invalidate();
		}

		private void mnuImagePaint_Click(object sender, EventArgs e)
		{
			mnuImageSelect.Checked = false;
			mnuImagePaint.Checked = true;
			mnuImageDraw.Checked = false;
			mnuImageLine.Checked = false;
			_tool = TypesOfTool.Paint;
		}

		private void mnuImageDraw_Click(object sender, EventArgs e)
		{
			mnuImageSelect.Checked = false;
			mnuImagePaint.Checked = false;
			mnuImageDraw.Checked = true;
			mnuImageLine.Checked = false;
			_tool = TypesOfTool.Draw;
		}

		private void mnuImageLine_Click(object sender, EventArgs e)
		{
			mnuImageSelect.Checked = false;
			mnuImagePaint.Checked = false;
			mnuImageDraw.Checked = false;
			mnuImageLine.Checked = true;
			_tool = TypesOfTool.Line;
		}

		private void mnuImageRadius01_Click(object sender, EventArgs e)
		{
			mnuImageRadius.Text = "&Radius (1.0)";
			_radius = 1.0f;
		}

		private void mnuImageRadius02_Click(object sender, EventArgs e)
		{
			mnuImageRadius.Text = "&Radius (2.0)";
			_radius = 2.0f;
		}

		private void mnuImageRadius03_Click(object sender, EventArgs e)
		{
			mnuImageRadius.Text = "&Radius (3.0)";
			_radius = 3.0f;
		}

		private void mnuImageRadius04_Click(object sender, EventArgs e)
		{
			mnuImageRadius.Text = "&Radius (4.0)";
			_radius = 4.0f;
		}

		private void mnuImageRadius05_Click(object sender, EventArgs e)
		{
			mnuImageRadius.Text = "&Radius (5.0)";
			_radius = 5.0f;
		}

		private void mnuImageRadius10_Click(object sender, EventArgs e)
		{
			mnuImageRadius.Text = "&Radius (10.0)";
			_radius = 10.0f;
		}

		private void mnuImageRadius15_Click(object sender, EventArgs e)
		{
			mnuImageRadius.Text = "&Radius (15.0)";
			_radius = 15.0f;
		}

		private void mnuImageRadius20_Click(object sender, EventArgs e)
		{
			mnuImageRadius.Text = "&Radius (20.0)";
			_radius = 20.0f;
		}

		private void mnuImageRadius50_Click(object sender, EventArgs e)
		{
			mnuImageRadius.Text = "&Radius (50.0)";
			_radius = 50.0f;
		}

		private void mnuImageRadiusInc_Click(object sender, EventArgs e)
		{
			_radius += 0.1f;
			mnuImageRadius.Text = "&Radius (" + _radius.ToString("0.0") + ")";
		}

		private void mnuImageRadiusDec_Click(object sender, EventArgs e)
		{
			_radius -= 0.1f;
			mnuImageRadius.Text = "&Radius (" + _radius.ToString("0.0") + ")";
		}

		private void mnuViewGrid_Click(object sender, EventArgs e)
		{
			picShape.Invalidate();
		}

		private void mnuView1to1_Click(object sender, EventArgs e)
		{
			float w = 1.0f;
			float h = (float)_shape.Height / _shape.Width;
			float ow = ClientSize.Height / h;
			w = (ClientSize.Width + ow) / 2;
			h *= w;

			Width = (int)(w + (Width - ClientSize.Width));
			Height = (int)(h + (Height - ClientSize.Height));

		}

	}
}