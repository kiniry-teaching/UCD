using System;
using System.Collections.Generic;
using System.Text;
using System.ComponentModel;

namespace ShArt
{

	[TypeConverter(typeof(ExpandableObjectConverter))]
	public class Pixel
	{

		protected int _x;
		protected int _y;
		protected float _radius = 0.0f;
		protected float _weight = 0.0f;
		protected float _falloff = 0.0f;
		protected List<Pixel> _neighbours = new List<Pixel>();

		[DescriptionAttribute("Cell X position"),
		 CategoryAttribute("Position")]
		public int X { get { return _x; } }
		[DescriptionAttribute("Cell Y position"),
		 CategoryAttribute("Position")]
		public int Y { get { return _y; } }

		[DefaultValueAttribute("8.0"),
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

	}

}
