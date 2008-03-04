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
		Line,
		Zone
	}

	public partial class frmShape: Form
	{

		protected Shape _shape;
		protected TypesOfTool _tool = TypesOfTool.Paint;
		protected float _radius = 5.0f;
		protected float _weight = 1.0f;
		protected float _falloff = 0.0f;
		protected float _mouseX = float.MinValue;
		protected float _mouseY = float.MinValue;
		protected int _zoneMode = 0;
		protected Zone _zone;

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
				trkWeight.Value = (int)(_shape.Dampen * trkWeight.Maximum);
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
			bool clear = false;

			if(_tool == TypesOfTool.Draw || _tool == TypesOfTool.Line || _tool == TypesOfTool.Paint)
				clear = SetPixelLock(_mouseX, _mouseY, true, true);

			for(int y = 0; y < _shape.Height; y++)
			for(int x = 0; x < _shape.Width; x++)
				SetNeighbourPixel(x, y, _shape.Pixels[x, y].Radius);

			for(int y = 0; y < _shape.Height; y++)
			for(int x = 0; x < _shape.Width; x++)
				if((we = CalculateWeight(_shape.Pixels[x, y])) > mwe)
					mwe = we;

			mwe = 1 / mwe;
			mwe = (1 - (1 - mwe) * (float)trkWeight.Value / 50);

			for(int y = 0; y < _shape.Height; y++)
			for(int x = 0; x < _shape.Width; x++)
			{
				we = CalculateWeight(_shape.Pixels[x, y]) * mwe;
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

				//e.Graphics.DrawRectangle(box, dx * 4, dy * 4, dx * (_shape.Width - 8), dy * (_shape.Height - 8));

			}

			if(mnuViewBound.Checked == true)
				e.Graphics.DrawRectangle(box, dx * _shape.HBound, dy * _shape.VBound, dx * (_shape.Width - _shape.HBound * 2), dy * (_shape.Height - _shape.VBound * 2));

			if(_tool == TypesOfTool.Draw || _tool == TypesOfTool.Line || _tool == TypesOfTool.Paint)
				if(clear == true)
					SetPixelLock(_mouseX, _mouseY, false, false);

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

		private void MapXY(ref float x, ref float y)
		{
			float w = picShape.ClientSize.Width;
			float h = picShape.ClientSize.Height;
			float dy = (h - 1) / _shape.Height;
			float dx = (w - 1) / _shape.Width;
			x = (int)(x / dx);
			y = (int)(y / dy);
		}

		private bool SetPixelLock(float mx, float my, bool draw, bool lck)
		{

			MapXY(ref mx, ref my);
			int x = (int)mx;
			int y = (int)my;
			
			if(x < 0 || x >= _shape.Width || y < 0 || y >= _shape.Height)
				return false;

			// If locked, don't do anything on written pixels
			if(lck == true)
				if(_shape.Pixels[x, y].Weight != 0)
					return false;

			if(draw == true)
				SetPixel(x, y, _radius, 1.0f, 0.0f);
			else
				SetPixel(x, y, 1.0f, 0.0f, 0.0f);
			picShape.Invalidate();

			return true;

		}

		private void picShape_MouseDown(object sender, MouseEventArgs e)
		{

			switch(_tool)
			{

				case TypesOfTool.Paint:
					if(e.Button == MouseButtons.Left || e.Button == MouseButtons.Right)
						if(e.Button == MouseButtons.Left)
							SetPixelLock(e.X, e.Y, true, false);
						else
							SetPixelLock(e.X, e.Y, false, false);
					break;

				case TypesOfTool.Zone:
					switch(_zoneMode)
					{
						case 0:
							_zone = new Zone();
							_zone.X = e.X;
							_zone.Y = e.Y;
							MapXY(_zone.X, _zone.Y);
							_shape.Zones.Add(_zone);
							_zoneMode = 1;
							break;
					}
					break;

			}

		}

		private void picShape_MouseUp(object sender, MouseEventArgs e)
		{

			if(_tool == TypesOfTool.Zone)
			{

				switch(_zoneMode)
				{
					case 0:
						break;
				}

			}

		}

		private void picShape_MouseMove(object sender, MouseEventArgs e)
		{
			_mouseX = e.X;
			_mouseY = e.Y;

			switch(_tool)
			{

				case TypesOfTool.Paint:
					if(e.Button != MouseButtons.None)
						picShape_MouseDown(sender, e);
					else
						picShape.Invalidate();
					break;

				case TypesOfTool.Zone:
					break;

			}

		}

		// x, y, radius, weight, falloff
		private void SetPixel(int cx, int cy, float r, float w, float f)
		{
			_shape.Pixels[cx, cy].Radius = r;
			_shape.Pixels[cx, cy].Weight = w;
			_shape.Pixels[cx, cy].Falloff = f;
			SetNeighbourPixel(cx, cy, r);

		}

		private void SetNeighbourPixel(int cx, int cy, float r)
		{
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
			w = ((ClientSize.Width - trkWeight.Width) + ow) / 2;
			h *= w;

			Width = (int)(w + (Width - ClientSize.Width + trkWeight.Width));
			Height = (int)(h + (Height - ClientSize.Height));

		}

		private void frmShape_Load(object sender, EventArgs e)
		{
			frmShape_Resize(null, null);
		}

		private void frmShape_Resize(object sender, EventArgs e)
		{
			picShape.Width = ClientSize.Width - trkWeight.Width;
			picShape.Height = ClientSize.Height;
			trkWeight.Height = ClientSize.Height;
			trkWeight.Left = ClientSize.Width - trkWeight.Width;
		}

		private void trkWeight_Scroll(object sender, EventArgs e)
		{
			_shape.Dampen = ((float)trkWeight.Value) / 50;
			Program.ShArt.pgdProperties.Refresh();
			picShape.Invalidate();
		}

		private void picShape_MouseLeave(object sender, EventArgs e)
		{
			_mouseX = float.MinValue;
			_mouseY = float.MinValue;
			picShape.Invalidate();
		}

		private void mnuZoneAdd_Click(object sender, EventArgs e)
		{
			_tool = TypesOfTool.Zone;
		}

		private void mnuViewBound_Click(object sender, EventArgs e)
		{
			picShape.Invalidate();
		}

	}
}