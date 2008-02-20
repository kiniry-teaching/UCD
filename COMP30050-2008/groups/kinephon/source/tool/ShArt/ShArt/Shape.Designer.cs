namespace ShArt
{
	partial class Shape
	{
		/// <summary>
		/// Required designer variable.
		/// </summary>
		private System.ComponentModel.IContainer components = null;

		/// <summary>
		/// Clean up any resources being used.
		/// </summary>
		/// <param name="disposing">true if managed resources should be disposed; otherwise, false.</param>
		protected override void Dispose(bool disposing)
		{
			if(disposing && (components != null))
			{
				components.Dispose();
			}
			base.Dispose(disposing);
		}

		#region Windows Form Designer generated code

		/// <summary>
		/// Required method for Designer support - do not modify
		/// the contents of this method with the code editor.
		/// </summary>
		private void InitializeComponent()
		{
			System.ComponentModel.ComponentResourceManager resources = new System.ComponentModel.ComponentResourceManager(typeof(Shape));
			this.picShape = new System.Windows.Forms.PictureBox();
			this.menuStrip1 = new System.Windows.Forms.MenuStrip();
			this.imageToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.gridXToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.drawToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem1 = new System.Windows.Forms.ToolStripSeparator();
			this.clearToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.zoneToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.penToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.fullToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem3 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem4 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem5 = new System.Windows.Forms.ToolStripMenuItem();
			this.clearToolStripMenuItem1 = new System.Windows.Forms.ToolStripMenuItem();
			this.selectZoneToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem2 = new System.Windows.Forms.ToolStripSeparator();
			this.widthToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem7 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem8 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem9 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem10 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem11 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem12 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem13 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem14 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem15 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem16 = new System.Windows.Forms.ToolStripMenuItem();
			this.cutToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.copyToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.pasteToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem6 = new System.Windows.Forms.ToolStripSeparator();
			this.toolStrip1 = new System.Windows.Forms.ToolStrip();
			this.toolStripButton1 = new System.Windows.Forms.ToolStripButton();
			((System.ComponentModel.ISupportInitialize)(this.picShape)).BeginInit();
			this.menuStrip1.SuspendLayout();
			this.toolStrip1.SuspendLayout();
			this.SuspendLayout();
			// 
			// picShape
			// 
			this.picShape.Dock = System.Windows.Forms.DockStyle.Fill;
			this.picShape.Location = new System.Drawing.Point(0, 0);
			this.picShape.Name = "picShape";
			this.picShape.Size = new System.Drawing.Size(300, 324);
			this.picShape.SizeMode = System.Windows.Forms.PictureBoxSizeMode.StretchImage;
			this.picShape.TabIndex = 0;
			this.picShape.TabStop = false;
			this.picShape.Paint += new System.Windows.Forms.PaintEventHandler(this.picShape_Paint);
			// 
			// menuStrip1
			// 
			this.menuStrip1.Dock = System.Windows.Forms.DockStyle.None;
			this.menuStrip1.Items.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.imageToolStripMenuItem});
			this.menuStrip1.Location = new System.Drawing.Point(8, 8);
			this.menuStrip1.Name = "menuStrip1";
			this.menuStrip1.Size = new System.Drawing.Size(45, 24);
			this.menuStrip1.TabIndex = 1;
			this.menuStrip1.Text = "menuStrip1";
			this.menuStrip1.Visible = false;
			// 
			// imageToolStripMenuItem
			// 
			this.imageToolStripMenuItem.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.gridXToolStripMenuItem,
            this.drawToolStripMenuItem,
            this.penToolStripMenuItem,
            this.widthToolStripMenuItem,
            this.toolStripMenuItem2,
            this.selectZoneToolStripMenuItem,
            this.zoneToolStripMenuItem,
            this.toolStripMenuItem1,
            this.cutToolStripMenuItem,
            this.copyToolStripMenuItem,
            this.pasteToolStripMenuItem,
            this.toolStripMenuItem6,
            this.clearToolStripMenuItem});
			this.imageToolStripMenuItem.MergeAction = System.Windows.Forms.MergeAction.Insert;
			this.imageToolStripMenuItem.MergeIndex = 1;
			this.imageToolStripMenuItem.Name = "imageToolStripMenuItem";
			this.imageToolStripMenuItem.Size = new System.Drawing.Size(37, 20);
			this.imageToolStripMenuItem.Text = "&Edit";
			// 
			// gridXToolStripMenuItem
			// 
			this.gridXToolStripMenuItem.Name = "gridXToolStripMenuItem";
			this.gridXToolStripMenuItem.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.S)));
			this.gridXToolStripMenuItem.Size = new System.Drawing.Size(179, 22);
			this.gridXToolStripMenuItem.Text = "&Select draw";
			this.gridXToolStripMenuItem.Click += new System.EventHandler(this.gridXToolStripMenuItem_Click);
			// 
			// drawToolStripMenuItem
			// 
			this.drawToolStripMenuItem.Name = "drawToolStripMenuItem";
			this.drawToolStripMenuItem.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.D)));
			this.drawToolStripMenuItem.Size = new System.Drawing.Size(179, 22);
			this.drawToolStripMenuItem.Text = "&Draw";
			// 
			// toolStripMenuItem1
			// 
			this.toolStripMenuItem1.Name = "toolStripMenuItem1";
			this.toolStripMenuItem1.Size = new System.Drawing.Size(149, 6);
			// 
			// clearToolStripMenuItem
			// 
			this.clearToolStripMenuItem.Name = "clearToolStripMenuItem";
			this.clearToolStripMenuItem.ShortcutKeys = System.Windows.Forms.Keys.Delete;
			this.clearToolStripMenuItem.Size = new System.Drawing.Size(179, 22);
			this.clearToolStripMenuItem.Text = "&Clear";
			// 
			// zoneToolStripMenuItem
			// 
			this.zoneToolStripMenuItem.Name = "zoneToolStripMenuItem";
			this.zoneToolStripMenuItem.Size = new System.Drawing.Size(152, 22);
			this.zoneToolStripMenuItem.Text = "&Zone";
			// 
			// penToolStripMenuItem
			// 
			this.penToolStripMenuItem.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.fullToolStripMenuItem,
            this.toolStripMenuItem3,
            this.toolStripMenuItem4,
            this.toolStripMenuItem5,
            this.clearToolStripMenuItem1});
			this.penToolStripMenuItem.Name = "penToolStripMenuItem";
			this.penToolStripMenuItem.ShortcutKeyDisplayString = "[/]";
			this.penToolStripMenuItem.Size = new System.Drawing.Size(179, 22);
			this.penToolStripMenuItem.Text = "  &Brush";
			// 
			// fullToolStripMenuItem
			// 
			this.fullToolStripMenuItem.Name = "fullToolStripMenuItem";
			this.fullToolStripMenuItem.Size = new System.Drawing.Size(152, 22);
			this.fullToolStripMenuItem.Text = "&100%";
			// 
			// toolStripMenuItem3
			// 
			this.toolStripMenuItem3.Name = "toolStripMenuItem3";
			this.toolStripMenuItem3.Size = new System.Drawing.Size(152, 22);
			this.toolStripMenuItem3.Text = "&75%";
			// 
			// toolStripMenuItem4
			// 
			this.toolStripMenuItem4.Name = "toolStripMenuItem4";
			this.toolStripMenuItem4.Size = new System.Drawing.Size(152, 22);
			this.toolStripMenuItem4.Text = "&50%";
			// 
			// toolStripMenuItem5
			// 
			this.toolStripMenuItem5.Name = "toolStripMenuItem5";
			this.toolStripMenuItem5.Size = new System.Drawing.Size(152, 22);
			this.toolStripMenuItem5.Text = "&25%";
			// 
			// clearToolStripMenuItem1
			// 
			this.clearToolStripMenuItem1.Name = "clearToolStripMenuItem1";
			this.clearToolStripMenuItem1.Size = new System.Drawing.Size(152, 22);
			this.clearToolStripMenuItem1.Text = "&Clear";
			// 
			// selectZoneToolStripMenuItem
			// 
			this.selectZoneToolStripMenuItem.Name = "selectZoneToolStripMenuItem";
			this.selectZoneToolStripMenuItem.Size = new System.Drawing.Size(152, 22);
			this.selectZoneToolStripMenuItem.Text = "S&elect zone";
			// 
			// toolStripMenuItem2
			// 
			this.toolStripMenuItem2.Name = "toolStripMenuItem2";
			this.toolStripMenuItem2.Size = new System.Drawing.Size(149, 6);
			// 
			// widthToolStripMenuItem
			// 
			this.widthToolStripMenuItem.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.toolStripMenuItem7,
            this.toolStripMenuItem8,
            this.toolStripMenuItem9,
            this.toolStripMenuItem10,
            this.toolStripMenuItem11,
            this.toolStripMenuItem12,
            this.toolStripMenuItem13,
            this.toolStripMenuItem14,
            this.toolStripMenuItem15,
            this.toolStripMenuItem16});
			this.widthToolStripMenuItem.Name = "widthToolStripMenuItem";
			this.widthToolStripMenuItem.ShortcutKeyDisplayString = "+/-";
			this.widthToolStripMenuItem.Size = new System.Drawing.Size(179, 22);
			this.widthToolStripMenuItem.Text = "  &Width";
			// 
			// toolStripMenuItem7
			// 
			this.toolStripMenuItem7.Name = "toolStripMenuItem7";
			this.toolStripMenuItem7.Size = new System.Drawing.Size(152, 22);
			this.toolStripMenuItem7.Text = "1";
			// 
			// toolStripMenuItem8
			// 
			this.toolStripMenuItem8.Name = "toolStripMenuItem8";
			this.toolStripMenuItem8.Size = new System.Drawing.Size(152, 22);
			this.toolStripMenuItem8.Text = "2";
			// 
			// toolStripMenuItem9
			// 
			this.toolStripMenuItem9.Name = "toolStripMenuItem9";
			this.toolStripMenuItem9.Size = new System.Drawing.Size(152, 22);
			this.toolStripMenuItem9.Text = "3";
			// 
			// toolStripMenuItem10
			// 
			this.toolStripMenuItem10.Name = "toolStripMenuItem10";
			this.toolStripMenuItem10.Size = new System.Drawing.Size(152, 22);
			this.toolStripMenuItem10.Text = "4";
			// 
			// toolStripMenuItem11
			// 
			this.toolStripMenuItem11.Name = "toolStripMenuItem11";
			this.toolStripMenuItem11.Size = new System.Drawing.Size(152, 22);
			this.toolStripMenuItem11.Text = "5";
			// 
			// toolStripMenuItem12
			// 
			this.toolStripMenuItem12.Name = "toolStripMenuItem12";
			this.toolStripMenuItem12.Size = new System.Drawing.Size(152, 22);
			this.toolStripMenuItem12.Text = "6";
			// 
			// toolStripMenuItem13
			// 
			this.toolStripMenuItem13.Name = "toolStripMenuItem13";
			this.toolStripMenuItem13.Size = new System.Drawing.Size(152, 22);
			this.toolStripMenuItem13.Text = "7";
			// 
			// toolStripMenuItem14
			// 
			this.toolStripMenuItem14.Name = "toolStripMenuItem14";
			this.toolStripMenuItem14.Size = new System.Drawing.Size(152, 22);
			this.toolStripMenuItem14.Text = "8";
			// 
			// toolStripMenuItem15
			// 
			this.toolStripMenuItem15.Name = "toolStripMenuItem15";
			this.toolStripMenuItem15.Size = new System.Drawing.Size(152, 22);
			this.toolStripMenuItem15.Text = "9";
			// 
			// toolStripMenuItem16
			// 
			this.toolStripMenuItem16.Name = "toolStripMenuItem16";
			this.toolStripMenuItem16.Size = new System.Drawing.Size(152, 22);
			this.toolStripMenuItem16.Text = "10";
			// 
			// cutToolStripMenuItem
			// 
			this.cutToolStripMenuItem.Name = "cutToolStripMenuItem";
			this.cutToolStripMenuItem.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.X)));
			this.cutToolStripMenuItem.Size = new System.Drawing.Size(179, 22);
			this.cutToolStripMenuItem.Text = "Cut";
			// 
			// copyToolStripMenuItem
			// 
			this.copyToolStripMenuItem.Name = "copyToolStripMenuItem";
			this.copyToolStripMenuItem.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.C)));
			this.copyToolStripMenuItem.Size = new System.Drawing.Size(179, 22);
			this.copyToolStripMenuItem.Text = "Copy";
			// 
			// pasteToolStripMenuItem
			// 
			this.pasteToolStripMenuItem.Name = "pasteToolStripMenuItem";
			this.pasteToolStripMenuItem.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.V)));
			this.pasteToolStripMenuItem.Size = new System.Drawing.Size(179, 22);
			this.pasteToolStripMenuItem.Text = "Paste";
			// 
			// toolStripMenuItem6
			// 
			this.toolStripMenuItem6.Name = "toolStripMenuItem6";
			this.toolStripMenuItem6.Size = new System.Drawing.Size(176, 6);
			// 
			// toolStrip1
			// 
			this.toolStrip1.Items.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.toolStripButton1});
			this.toolStrip1.Location = new System.Drawing.Point(0, 0);
			this.toolStrip1.Name = "toolStrip1";
			this.toolStrip1.Size = new System.Drawing.Size(300, 25);
			this.toolStrip1.TabIndex = 2;
			this.toolStrip1.Text = "toolStrip1";
			this.toolStrip1.Visible = false;
			// 
			// toolStripButton1
			// 
			this.toolStripButton1.DisplayStyle = System.Windows.Forms.ToolStripItemDisplayStyle.Image;
			this.toolStripButton1.Image = ((System.Drawing.Image)(resources.GetObject("toolStripButton1.Image")));
			this.toolStripButton1.ImageTransparentColor = System.Drawing.Color.Magenta;
			this.toolStripButton1.Name = "toolStripButton1";
			this.toolStripButton1.Size = new System.Drawing.Size(23, 22);
			this.toolStripButton1.Text = "toolStripButton1";
			// 
			// Shape
			// 
			this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
			this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
			this.ClientSize = new System.Drawing.Size(300, 324);
			this.Controls.Add(this.toolStrip1);
			this.Controls.Add(this.menuStrip1);
			this.Controls.Add(this.picShape);
			this.Font = new System.Drawing.Font("Tahoma", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
			this.MainMenuStrip = this.menuStrip1;
			this.Name = "Shape";
			this.Text = "Shape";
			((System.ComponentModel.ISupportInitialize)(this.picShape)).EndInit();
			this.menuStrip1.ResumeLayout(false);
			this.menuStrip1.PerformLayout();
			this.toolStrip1.ResumeLayout(false);
			this.toolStrip1.PerformLayout();
			this.ResumeLayout(false);
			this.PerformLayout();

		}

		#endregion

		private System.Windows.Forms.PictureBox picShape;
		private System.Windows.Forms.MenuStrip menuStrip1;
		private System.Windows.Forms.ToolStripMenuItem imageToolStripMenuItem;
		private System.Windows.Forms.ToolStripMenuItem gridXToolStripMenuItem;
		private System.Windows.Forms.ToolStripMenuItem drawToolStripMenuItem;
		private System.Windows.Forms.ToolStripMenuItem zoneToolStripMenuItem;
		private System.Windows.Forms.ToolStripSeparator toolStripMenuItem1;
		private System.Windows.Forms.ToolStripMenuItem clearToolStripMenuItem;
		private System.Windows.Forms.ToolStripMenuItem penToolStripMenuItem;
		private System.Windows.Forms.ToolStripMenuItem fullToolStripMenuItem;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem3;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem4;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem5;
		private System.Windows.Forms.ToolStripMenuItem clearToolStripMenuItem1;
		private System.Windows.Forms.ToolStripSeparator toolStripMenuItem2;
		private System.Windows.Forms.ToolStripMenuItem selectZoneToolStripMenuItem;
		private System.Windows.Forms.ToolStripMenuItem widthToolStripMenuItem;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem7;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem8;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem9;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem10;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem11;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem12;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem13;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem14;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem15;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem16;
		private System.Windows.Forms.ToolStripMenuItem cutToolStripMenuItem;
		private System.Windows.Forms.ToolStripMenuItem copyToolStripMenuItem;
		private System.Windows.Forms.ToolStripMenuItem pasteToolStripMenuItem;
		private System.Windows.Forms.ToolStripSeparator toolStripMenuItem6;
		private System.Windows.Forms.ToolStripButton toolStripButton1;
		public System.Windows.Forms.ToolStrip toolStrip1;
	}
}