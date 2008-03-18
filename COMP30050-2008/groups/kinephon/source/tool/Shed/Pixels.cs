using System;
using System.Collections.Generic;
using System.Text;

namespace Shed
{

	public class Pixels
	{

		protected Shape _shape;
		protected Pixel[,] _pixels;

		public Pixels(Shape shape)
		{	_shape = shape;
		}

		public Pixel[,] Pixel
		{
			get { return _pixels; }
		}

		public void CalculateNeighbours()
		{

			for(int y = 0; y < _shape.Height; y++)
			for(int x = 0; x < _shape.Width; x++)
				CalculateNeighbour(x, y, _pixels[x, y].Radius);

		}

		private void CalculateNeighbour(int cx, int cy, float r)
		{
			for(int y = cy - (int)Math.Floor(r); y < cy + (int)Math.Ceiling(r); y++)
			for(int x = cx - (int)Math.Floor(r); x < cx + (int)Math.Ceiling(r); x++)
				if(!(x == cx && y == cy))
					AddNeighbour(x, y, _pixels[cx, cy]);
		}

		private void AddNeighbour(int x, int y, Pixel n)
		{
			if(x >= 0 && y >= 0 && x < _shape.Width && y < _shape.Height)
				if(_pixels[x, y].Neighbours.Contains(n) == false)
					_pixels[x, y].Neighbours.Add(n);
		}

		public void CreatePixels(int w, int h)
		{
			Pixel[,] pixels = new Pixel[w, h];
			for(int y = 0; y < h; y++)
			for(int x = 0; x < w; x++)
				pixels[x, y] = new Pixel(x, y);

			if(_pixels != null)
				for(int y = 0; y < Math.Min(h, _shape.Height); y++)
				for(int x = 0; x < Math.Min(w, _shape.Width); x++)
					pixels[x, y] = _pixels[x, y];

			_pixels = pixels;

		}

	}

}
