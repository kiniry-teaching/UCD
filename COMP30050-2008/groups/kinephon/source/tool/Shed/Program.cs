using System;
using System.Collections.Generic;
using System.Windows.Forms;

namespace Shed
{
	static class Program
	{
		public static frmShed Shed;
		/// <summary>
		/// The main entry point for the application.
		/// </summary>
		[STAThread]
		static void Main()
		{
			Application.EnableVisualStyles();
			Application.SetCompatibleTextRenderingDefault(false);
			KBHook.SetHook();
			Application.Run(Shed = new frmShed());
			KBHook.Unhook();
		}
	}
}