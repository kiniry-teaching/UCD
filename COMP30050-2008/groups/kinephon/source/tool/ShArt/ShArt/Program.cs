using System;
using System.Collections.Generic;
using System.Windows.Forms;

namespace ShArt
{
	static class Program
	{
		public static frmShArt ShArt;
		/// <summary>
		/// The main entry point for the application.
		/// </summary>
		[STAThread]
		static void Main()
		{
			Application.EnableVisualStyles();
			Application.SetCompatibleTextRenderingDefault(false);
			Application.Run(ShArt = new frmShArt());
		}
	}
}