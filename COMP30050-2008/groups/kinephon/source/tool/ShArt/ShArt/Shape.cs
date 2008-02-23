using System;
using System.Collections.Generic;
using System.Text;
using System.Windows.Forms;
using System.ComponentModel;
using System.Drawing;

namespace ShArt
{

	public enum TypesOfShape
	{
		Movement,
		Speed,
		Acceleration
	}

	public class Shape
	{
		protected TreeNode _node;
		protected Rectangle _windowPosition;
		protected frmShape _form;
		protected TypesOfShape _type;
		protected int _width;
		protected int _height;
		protected Zones _zones;
		protected Pixel[,] _pixels;

		public Shape(TreeNode node)
		{
			_node = node;
			_node.Tag = this;
			_width = 32;
			_height = 32;
			_type = TypesOfShape.Movement;
			_zones = new Zones();
			CreatePixels(_width, _height);
		}

		[BrowsableAttribute(false)]
		public TreeNode Node
		{
			get { return _node; }
		}
		
		[BrowsableAttribute(false)]
		public frmShape Form
		{
			get { return _form; }
			set { _form = value; }
		}
		
		[BrowsableAttribute(false)]
		public Rectangle WindowPosition
		{
			get { return _windowPosition; }
			set { _windowPosition = value; }
		}

		[BrowsableAttribute(false)]
		public Pixel[,] Pixels
		{
			get { return _pixels; }
		}

		[DefaultValueAttribute("New Shape"),
		 DescriptionAttribute("Name to help remember this shape during editing"),
		 CategoryAttribute("Details")]
		public string Name
		{
			get { return _node.Text; }
			set
			{	_node.Text = value;
				if(_form != null)
					_form.Shape = this;
			}
		}

		[DefaultValueAttribute(TypesOfShape.Movement),
		 DescriptionAttribute("Does this shape describe a movement, speed, or acceleration"),
		 CategoryAttribute("Details")]
		public TypesOfShape Type
		{
			get { return _type; }
			set { _type = value; }
		}

		[DefaultValueAttribute(32),
		 DescriptionAttribute("Number of vertical cells"),
		 CategoryAttribute("Grid")]
		public int Width
		{
			get { return _width; }
			set
			{
				if(value < 16)
					throw new Exception("Too small");
				CreatePixels(value, _height);
				_width = value;
				if(_form != null)
					_form.Shape = this;
			}
		}

		[DefaultValueAttribute(32),
		 DescriptionAttribute("Number of horizontal cells"),
		 CategoryAttribute("Grid")]
		public int Height
		{
			get { return _height; }
			set
			{
				if(value < 16)
					throw new Exception("Too small");
				CreatePixels(_width, value);
				_height = value;
				if(_form != null)
					_form.Shape = this;
			}
		}

		[TypeConverter(typeof(ExpandableObjectConverter)),
		 DescriptionAttribute("Zones"),
		 CategoryAttribute("Grid")]
		public Zones Zones
		{
			get { return _zones; }
		}

		protected void CreatePixels(int w, int h)
		{
			Pixel[,] pixels = new Pixel[w, h];
			for(int y = 0; y < h; y++)
			for(int x = 0; x < w; x++)
				pixels[x, y] = new Pixel();

			if(_pixels != null)
				for(int y = 0; y < Math.Min(h, _height); y++)
				for(int x = 0; x < Math.Min(w, _width); x++)
					pixels[x, y] = _pixels[x, y];

			_pixels = pixels;

		}

	}

}
