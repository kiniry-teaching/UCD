using System;
using System.Collections;
using System.Collections.Generic;
using System.Text;
using System.ComponentModel;

namespace Shed
{

	public class Zones : List<Zone>, ICustomTypeDescriptor
	{

		public String GetClassName()
		{
			return TypeDescriptor.GetClassName(this, true);
		}

		public AttributeCollection GetAttributes()
		{
			return TypeDescriptor.GetAttributes(this, true);
		}

		public String GetComponentName()
		{
			return TypeDescriptor.GetComponentName(this, true);
		}

		public TypeConverter GetConverter()
		{
			return TypeDescriptor.GetConverter(this, true);
		}

		public EventDescriptor GetDefaultEvent() 
		{
			return TypeDescriptor.GetDefaultEvent(this, true);
		}

		public PropertyDescriptor GetDefaultProperty() 
		{
			return TypeDescriptor.GetDefaultProperty(this, true);
		}

		public object GetEditor(Type editorBaseType) 
		{
			return TypeDescriptor.GetEditor(this, editorBaseType, true);
		}

		public EventDescriptorCollection GetEvents(Attribute[] attributes) 
		{
			return TypeDescriptor.GetEvents(this, attributes, true);
		}

		public EventDescriptorCollection GetEvents()
		{
			return TypeDescriptor.GetEvents(this, true);
		}

		public object GetPropertyOwner(PropertyDescriptor pd) 
		{
			return this;
		}

		public PropertyDescriptorCollection GetProperties(Attribute[] attributes)
		{
			return GetProperties();
		}
		
		public PropertyDescriptorCollection GetProperties() 
		{
			// Create a new collection object PropertyDescriptorCollection
			PropertyDescriptorCollection pds = new PropertyDescriptorCollection(null);

			// Iterate the list of employees
			for(int i = 0; i < Count; i++)
				pds.Add(new ZonesPD(this, i));

			return pds;
		}
		
	}

	public class ZonesPD : PropertyDescriptor
	{

		protected Zones _zones = null;
		protected int _index = -1;

		public ZonesPD(Zones zones, int index) : base("#" + index.ToString(), null)
		{
			_zones = zones;
			_index = index;
		}

		public override AttributeCollection Attributes { get { return new AttributeCollection(null); } }
		public override bool CanResetValue(object component) { return true; }
		public override Type ComponentType { get { return _zones.GetType(); } }

		public override string DisplayName { get { return "Zone"; } }

		public override string Description
		{
			get
			{
				Zone zone = _zones[_index];
				StringBuilder sb = new StringBuilder();
				sb.Append(zone.Order + ": (" + zone.X + ", " + zone.Y + ") ");
				sb.Append("[" + zone.EnterRadius);
				sb.Append(",");
				sb.Append(zone.EnterAngle);
				sb.Append(",");
				sb.Append(zone.EnterArc + "]");
				sb.Append("; [");
				sb.Append(zone.ExitRadius);
				sb.Append(",");
				sb.Append(zone.ExitAngle);
				sb.Append(",");
				sb.Append(zone.ExitArc);
				sb.Append("]");

				return sb.ToString();
			}
		}

		public override object GetValue(object component) { return _zones[_index]; }
		public override bool IsReadOnly { get { return true; } }
		public override string Name { get { return "#" + _index.ToString(); } }
		public override Type PropertyType { get { return _zones[_index].GetType(); } }
		public override void ResetValue(object component) {}
		public override bool ShouldSerializeValue(object component) { return true; }
		public override void SetValue(object component, object value) { /* this.collection[index] = value; */ }

	}

	public class ZoneComparer : Comparer<Zone>
	{
		public override int Compare(Zone x, Zone y)
		{
			if(x.Order == y.Order)
				return 0;
			else
			if(x.Order < y.Order)
				return -1;
			else
				return 1;
		}
	}

}
