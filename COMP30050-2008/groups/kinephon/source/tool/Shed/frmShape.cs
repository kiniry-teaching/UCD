using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.Threading;

namespace Shed
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
			setPaintStatus(stsBrush, _weight, _radius, _falloff);
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

			// Calculate maximum dimming amount
			if(mnuViewGlow.Checked == true)
			{

				for(int y = 0; y < _shape.Height; y++)
				for(int x = 0; x < _shape.Width; x++)
					SetNeighbourPixel(x, y, _shape.Pixels[x, y].Radius);

				for(int y = 0; y < _shape.Height; y++)
				for(int x = 0; x < _shape.Width; x++)
					if((we = CalculateWeight(_shape.Pixels[x, y])) > mwe)
						mwe = we;

				mwe = 1 / mwe;
				mwe = (1 - (1 - mwe) * (float)trkWeight.Value / 50);

			}

			for(int y = 0; y < _shape.Height; y++)
			for(int x = 0; x < _shape.Width; x++)
			{
				r = 0;
				g = 0;
				// Calculate glow
				if(mnuViewGlow.Checked == true)
				{

					we = CalculateWeight(_shape.Pixels[x, y]) * mwe;
					if(we < -1) we = -1;
					if(we >  1) we = 1;

				}
				else
					we = _shape.Pixels[x, y].Weight;

				if(we < 0)
					if(mnuViewNegative.Checked == true)
						r = (int)(62 * (-we));
					else
						r = 0;
				else
					g = (int)(62 * we);

				// Add or remove a blue tint to the centre pixel
				if(mnuViewPixel.Checked == true)
					if(_shape.Pixels[x, y].Weight > 0)
						b = 62;
					else
					if(_shape.Pixels[x, y].Weight < 0)
						if(mnuViewNegative.Checked == true)
							b = -62;
						else
							b = 0;
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

			if(mnuViewZone.Checked == true)
			{
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
				SetPixel(x, y, _radius, _weight, _falloff);
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
							float mx = e.X, my = e.Y;
							MapXY(ref mx, ref my);
							_zone.X = mx;
							_zone.Y = my;
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

			float fx = e.X, fy = e.Y;
			MapXY(ref fx, ref fy);
			int x = (int)fx, y = (int)fy;
			if(x >= 0 && y >= 0 && x < _shape.Width && y < _shape.Height)
			{
				stsCoords.Text = x.ToString("0") + ", " + y.ToString("0");
				setPaintStatus(stsCanvas, _shape.Pixels[x, y].Weight, _shape.Pixels[x, y].Radius, _shape.Pixels[x, y].Falloff);
			}

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
			stsTool.Text = "Paint";
		}

		private void mnuImageDraw_Click(object sender, EventArgs e)
		{
			mnuImageSelect.Checked = false;
			mnuImagePaint.Checked = false;
			mnuImageDraw.Checked = true;
			mnuImageLine.Checked = false;
			_tool = TypesOfTool.Draw;
			stsTool.Text = "Draw";
		}

		private void mnuImageLine_Click(object sender, EventArgs e)
		{
			mnuImageSelect.Checked = false;
			mnuImagePaint.Checked = false;
			mnuImageDraw.Checked = false;
			mnuImageLine.Checked = true;
			_tool = TypesOfTool.Line;
			stsTool.Text = "Line";
		}

		private void mnuViewGrid_Click(object sender, EventArgs e)
		{
			picShape.Invalidate();
		}

		private void mnuView1to1_Click(object sender, EventArgs e)
		{
			float w = 1.0f;
			float h = (float)_shape.Height / _shape.Width;
			float ow = (ClientSize.Height - stsStatus.Height) / h;
			w = ((ClientSize.Width - trkWeight.Width) + ow) / 2;
			h *= w;

			Width = (int)(w + (Width - ClientSize.Width + trkWeight.Width));
			Height = (int)(h + (Height - ClientSize.Height +stsStatus.Height));

		}

		private void frmShape_Load(object sender, EventArgs e)
		{
			frmShape_Resize(null, null);
		}

		private void frmShape_Resize(object sender, EventArgs e)
		{
			picShape.Width = ClientSize.Width - trkWeight.Width;
			picShape.Height = ClientSize.Height - stsStatus.Height;
			trkWeight.Height = ClientSize.Height - stsStatus.Height;
			trkWeight.Left = ClientSize.Width - trkWeight.Width;
		}

		private void trkWeight_Scroll(object sender, EventArgs e)
		{
			_shape.Dampen = ((float)trkWeight.Value) / 50;
			Program.Shed.pgdProperties.Refresh();
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
			stsTool.Text = "Zone";
		}

		private void mnuViewBound_Click(object sender, EventArgs e)
		{
			picShape.Invalidate();
		}

		private void mnuViewGlow_Click(object sender, EventArgs e)
		{
			picShape.Invalidate();
		}

		private void mnuViewPixel_Click(object sender, EventArgs e)
		{
			picShape.Invalidate();
		}

		private void mnuViewZone_Click(object sender, EventArgs e)
		{
			picShape.Invalidate();
		}

		#region mnuImageRadius
		private void mnuImageRadius01_Click(object sender, EventArgs e)
		{
			mnuImageRadius.Text = "&Radius (1.0)";
			_radius = 1.0f;
			setPaintStatus(stsBrush, _weight, _radius, _falloff);
		}

		private void mnuImageRadius02_Click(object sender, EventArgs e)
		{
			mnuImageRadius.Text = "&Radius (2.0)";
			_radius = 2.0f;
			setPaintStatus(stsBrush, _weight, _radius, _falloff);
		}

		private void mnuImageRadius03_Click(object sender, EventArgs e)
		{
			mnuImageRadius.Text = "&Radius (3.0)";
			_radius = 3.0f;
			setPaintStatus(stsBrush, _weight, _radius, _falloff);
		}

		private void mnuImageRadius04_Click(object sender, EventArgs e)
		{
			mnuImageRadius.Text = "&Radius (4.0)";
			_radius = 4.0f;
			setPaintStatus(stsBrush, _weight, _radius, _falloff);
		}

		private void mnuImageRadius05_Click(object sender, EventArgs e)
		{
			mnuImageRadius.Text = "&Radius (5.0)";
			_radius = 5.0f;
			setPaintStatus(stsBrush, _weight, _radius, _falloff);
		}

		private void mnuImageRadius10_Click(object sender, EventArgs e)
		{
			mnuImageRadius.Text = "&Radius (10.0)";
			_radius = 10.0f;
			setPaintStatus(stsBrush, _weight, _radius, _falloff);
		}

		private void mnuImageRadius15_Click(object sender, EventArgs e)
		{
			mnuImageRadius.Text = "&Radius (15.0)";
			_radius = 15.0f;
			setPaintStatus(stsBrush, _weight, _radius, _falloff);
		}

		private void mnuImageRadius20_Click(object sender, EventArgs e)
		{
			mnuImageRadius.Text = "&Radius (20.0)";
			_radius = 20.0f;
			setPaintStatus(stsBrush, _weight, _radius, _falloff);
		}

		private void mnuImageRadius50_Click(object sender, EventArgs e)
		{
			mnuImageRadius.Text = "&Radius (50.0)";
			_radius = 50.0f;
			setPaintStatus(stsBrush, _weight, _radius, _falloff);
		}

		public void mnuImageRadiusInc_Click(object sender, EventArgs e)
		{
			_radius += 0.1f;
			mnuImageRadius.Text = "&Radius (" + _radius.ToString("0.0") + ")";
			setPaintStatus(stsBrush, _weight, _radius, _falloff);
		}

		public void mnuImageRadiusDec_Click(object sender, EventArgs e)
		{
			_radius -= 0.1f;
			mnuImageRadius.Text = "&Radius (" + _radius.ToString("0.0") + ")";
			setPaintStatus(stsBrush, _weight, _radius, _falloff);
		}
		#endregion
		#region mnuImageWeight
		private void mnuImageWeight4_Click(object sender, EventArgs e)
		{
			mnuImageWeight.Text = "&Weight (1.0)";
			_weight = 1.0f;
			setPaintStatus(stsBrush, _weight, _radius, _falloff);
		}

		private void mnuImageWeight3_Click(object sender, EventArgs e)
		{
			mnuImageWeight.Text = "&Weight (0.5)";
			_weight = 0.5f;
			setPaintStatus(stsBrush, _weight, _radius, _falloff);
		}

		private void mnuImageWeight2_Click(object sender, EventArgs e)
		{
			mnuImageWeight.Text = "&Weight (0.0)";
			_weight = 0.0f;
			setPaintStatus(stsBrush, _weight, _radius, _falloff);
		}

		private void mnuImageWeight1_Click(object sender, EventArgs e)
		{
			mnuImageWeight.Text = "&Weight (-0.5)";
			_weight = -0.5f;
			setPaintStatus(stsBrush, _weight, _radius, _falloff);
		}

		private void mnuImageWeight0_Click(object sender, EventArgs e)
		{
			mnuImageWeight.Text = "&Weight (-1.0)";
			_weight = -1.0f;
			setPaintStatus(stsBrush, _weight, _radius, _falloff);
		}

		public void mnuImageWeightInc_Click(object sender, EventArgs e)
		{
			_weight += 0.1f;
			if(_weight > 1)
				_weight = 1;
			mnuImageWeight.Text = "&Weight (" + _weight.ToString("0.0") + ")";
			setPaintStatus(stsBrush, _weight, _radius, _falloff);
		}

		public void mnuImageWeightDec_Click(object sender, EventArgs e)
		{
			_weight -= 0.1f;
			if(_weight < -1)
				_weight = -1;
			mnuImageWeight.Text = "&Weight (" + _weight.ToString("0.0") + ")";
			setPaintStatus(stsBrush, _weight, _radius, _falloff);
		}
		#endregion

		private void setPaintStatus(ToolStripStatusLabel sts, float weight, float radius, float falloff)
		{
			sts.Text = weight.ToString("0.0") + ", " + radius.ToString("0.0") + ", " + falloff.ToString("0.0");
		}

		private void mnuViewNegative_Click(object sender, EventArgs e)
		{
			picShape.Invalidate();
		}

		private void frmShape_KeyDown(object sender, KeyEventArgs e)
		{
			if(e.KeyCode == Keys.Subtract)
				mnuImageWeightInc_Click(null, null);
		}

		private void frmShape_Activated(object sender, EventArgs e)
		{
			
		}

		private void frmShape_PreviewKeyDown(object sender, PreviewKeyDownEventArgs e)
		{
			;
		}

		private void trkWeight_PreviewKeyDown(object sender, PreviewKeyDownEventArgs e)
		{
			;
		}

	}
}