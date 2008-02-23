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
		protected frmShape _form;
		protected TypesOfShape _type;
		protected int _width;
		protected int _height;
		protected Rectangle _windowPosition;

		public Shape(TreeNode node)
		{
			_node = node;
			_node.Tag = this;
			_width = 32;
			_height = 32;
			_type = TypesOfShape.Movement;
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

		[DefaultValueAttribute("New Shape"),
		 DescriptionAttribute("Name to help remember this shape during editing")]
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
		 DescriptionAttribute("Does this shape describe a movement, speed, or acceleration")]
		public TypesOfShape Type
		{
			get { return _type; }
			set { _type = value; }
		}

		[DefaultValueAttribute(32),
		 DescriptionAttribute("Number of vertical cells")]
		public int Width
		{
			get { return _width; }
			set
			{
				if(value < 16)
					throw new Exception("Too small");
				_width = value;
				if(_form != null)
					_form.Shape = this;
			}
		}

		[DefaultValueAttribute(32),
		 DescriptionAttribute("Number of horizontal cells")]
		public int Height
		{
			get { return _height; }
			set
			{
				if(value < 16)
					throw new Exception("Too small");
				_height = value;
				if(_form != null)
					_form.Shape = this;
			}
		}

	}

}
