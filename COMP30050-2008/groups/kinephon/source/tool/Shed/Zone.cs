using System;
using System.Collections.Generic;
using System.Text;
using System.ComponentModel;

namespace Shed
{

	[TypeConverter(typeof(ZoneConverter))]
	public class Zone
	{

		protected float _x;
		protected float _y;
		protected float _enterRadius;
		protected float _enterAngle;
		protected float _enterArc;
		protected float _exitRadius;
		protected float _exitAngle;
		protected float _exitArc;
		protected int _order;

		[DescriptionAttribute("X position of zone"),
		 CategoryAttribute("Position")]
		public float X
		{
			get { return _x; }
			set { _x = value; }
		}

		[DescriptionAttribute("Y position of zone"),
		 CategoryAttribute("Position")]
		public float Y
		{
			get { return _y; }
			set { _y = value; }
		}

		[DescriptionAttribute("Radius from centre before a point is inside"),
		 CategoryAttribute("Radius")]
		public float EnterRadius
		{
			get { return _enterRadius; }
			set { _enterRadius = value; }
		}

		[DescriptionAttribute("Centre angle of where point can enter"),
		 CategoryAttribute("Angle")]
		public float EnterAngle
		{
			get { return _enterAngle; }
			set { _enterAngle = value; }
		}

		[DescriptionAttribute("Angle range off of EnterAngle between which point can enter"),
		 CategoryAttribute("Angle")]
		public float EnterArc
		{
			get { return _enterArc; }
			set { _enterArc = value; }
		}

		[DescriptionAttribute("Radius from centre before a point is outside"),
		 CategoryAttribute("Radius")]
		public float ExitRadius
		{
			get { return _exitRadius; }
			set { _exitRadius = value; }
		}

		[DescriptionAttribute("Centre angle of where point can exit"),
		 CategoryAttribute("Angle")]
		public float ExitAngle
		{
			get { return _exitAngle; }
			set { _exitAngle = value; }
		}

		[DescriptionAttribute("Angle range off of ExitAngle between which point can exit"),
		 CategoryAttribute("Angle")]
		public float ExitArc
		{
			get { return _exitArc; }
			set { _exitArc = value; }
		}

		[DescriptionAttribute("Ordering in all zones of which this zone must be entered"),
		 CategoryAttribute("Position")]
		public int Order
		{
			get { return _order; }
			set { _order = value; }
		}

	}

	internal class ZoneConverter : ExpandableObjectConverter
	{

		public override object ConvertTo
		(	ITypeDescriptorContext context,
			System.Globalization.CultureInfo culture,
			object value,
			Type destinationType
		){

			if(destinationType == typeof(string) && value is Zone)
			{
				Zone zone = (Zone)value;
				return zone.Order + ": (" + zone.X + ", " + zone.Y + ")";
			}

			return base.ConvertTo(context, culture, value, destinationType);
		}

	}

}
