using System;
using System.Collections.Generic;
using System.Text;
using System.ComponentModel;

namespace Shed
{

	[TypeConverter(typeof(ExpandableObjectConverter))]
	public class Pixel
	{

		protected int _x;
		protected int _y;
		protected float _radius = 1.0f;
		protected float _weight = 0.0f;
		protected float _falloff = 0.0f;
		protected List<Pixel> _neighbours = new List<Pixel>();

		public Pixel(int x, int y)
		{
			_x = x;
			_y = y;
		}

		[DescriptionAttribute("Cell X position"),
		 CategoryAttribute("Position")]
		public int X { get { return _x; } }
		[DescriptionAttribute("Cell Y position"),
		 CategoryAttribute("Position")]
		public int Y { get { return _y; } }

		[DefaultValueAttribute("4.0"),
		 DescriptionAttribute("Radius of affected cells"),
		 CategoryAttribute("Weight")]
		public float Radius
		{
			get { return _radius; }
			set
			{
				if(value < 1)
					throw new Exception("Too small");
				_radius = value;
			}
		}

		[DefaultValueAttribute("1.0"),
		 DescriptionAttribute("Weight of this cell"),
		 CategoryAttribute("Weight")]
		public float Weight
		{
			get { return _weight; }
			set
			{
				if(value < -1 || value > 1)
					throw new Exception("Must be in the range -1..1");
				_weight = value;
			}
		}

		[DefaultValueAttribute("0.0"),
		 DescriptionAttribute("Curve of falloff"),
		 CategoryAttribute("Weight")]
		public float Falloff
		{
			get { return _falloff; }
			set
			{
				if(value < -1 || value > 1)
					throw new Exception("Must be in the range -1..1");
				_falloff = value;
			}
		}

		[DefaultValueAttribute("0.0"),
		 DescriptionAttribute("Weight added by neighbours"),
		 CategoryAttribute("Weight")]
		public List<Pixel> Neighbours
		{
			get { return _neighbours; }
		}

		public void Set(float r, float w, float f)
		{
			_radius = r;
			_weight = w;
			_falloff = f;
		}

		public float CalculateWeight(float DimWeight, float min, float max)
		{

			float d;
			float w = _weight;
			Pixel np;

			if(_neighbours != null && _neighbours.Count != 0)
				for(int i = 0; i < _neighbours.Count; i++)
				{

					np = _neighbours[i];

					d = Distance(_x, _y, np.X, np.Y);

					if(d > np.Radius)
					{	// Too far away - don't consider this neighbour again
						_neighbours.Remove(np);
						i--;
					}
					else
						w += (1 - (d / np.Radius)) * np.Weight;

				}

			w *= DimWeight;

			if(w < min) w = min;
			if(w > max) w = max;

			return w;

		}

		private float Distance(int x, int y, int u, int v)
		{

			int dx = u - x;
			int dy = v - y;

			return (float)Math.Sqrt(dx * dx + dy * dy);

		}

	}

}
