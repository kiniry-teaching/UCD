namespace ShArt
{
	partial class frmShape
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
			System.Windows.Forms.ToolStripSeparator mnuImageDiv2;
			System.Windows.Forms.ToolStripSeparator mnuImageDiv3;
			System.Windows.Forms.ToolStripSeparator mnuImageDiv1;
			System.ComponentModel.ComponentResourceManager resources = new System.ComponentModel.ComponentResourceManager(typeof(frmShape));
			this.picShape = new System.Windows.Forms.PictureBox();
			this.mnuShape = new System.Windows.Forms.MenuStrip();
			this.mnuImage = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuImageSelect = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuImageSelectAll = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuImagePaint = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuImageRadius = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem3 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem4 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem5 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem7 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem8 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem2 = new System.Windows.Forms.ToolStripSeparator();
			this.toolStripMenuItem10 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem11 = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuImageWeight = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem12 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem13 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem14 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem15 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem16 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem9 = new System.Windows.Forms.ToolStripSeparator();
			this.increaseToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.decreaseToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.falloff00ToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem6 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem17 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem18 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem19 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem20 = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem1 = new System.Windows.Forms.ToolStripSeparator();
			this.increaseToolStripMenuItem1 = new System.Windows.Forms.ToolStripMenuItem();
			this.decreaseToolStripMenuItem1 = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuImageCut = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuImageCopy = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuImagePaste = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuImageClear = new System.Windows.Forms.ToolStripMenuItem();
			this.areaToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.selectToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.selectAllToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem21 = new System.Windows.Forms.ToolStripSeparator();
			this.addToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.deleteToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.toolStripMenuItem22 = new System.Windows.Forms.ToolStripSeparator();
			this.tbrShape = new System.Windows.Forms.ToolStrip();
			this.toolStripButton1 = new System.Windows.Forms.ToolStripButton();
			mnuImageDiv2 = new System.Windows.Forms.ToolStripSeparator();
			mnuImageDiv3 = new System.Windows.Forms.ToolStripSeparator();
			mnuImageDiv1 = new System.Windows.Forms.ToolStripSeparator();
			((System.ComponentModel.ISupportInitialize)(this.picShape)).BeginInit();
			this.mnuShape.SuspendLayout();
			this.tbrShape.SuspendLayout();
			this.SuspendLayout();
			// 
			// mnuImageDiv2
			// 
			mnuImageDiv2.Name = "mnuImageDiv2";
			mnuImageDiv2.Size = new System.Drawing.Size(147, 6);
			// 
			// mnuImageDiv3
			// 
			mnuImageDiv3.Name = "mnuImageDiv3";
			mnuImageDiv3.Size = new System.Drawing.Size(147, 6);
			// 
			// mnuImageDiv1
			// 
			mnuImageDiv1.Name = "mnuImageDiv1";
			mnuImageDiv1.Size = new System.Drawing.Size(147, 6);
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
			// mnuShape
			// 
			this.mnuShape.Dock = System.Windows.Forms.DockStyle.None;
			this.mnuShape.Items.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.mnuImage,
            this.areaToolStripMenuItem});
			this.mnuShape.Location = new System.Drawing.Point(8, 8);
			this.mnuShape.Name = "mnuShape";
			this.mnuShape.Size = new System.Drawing.Size(100, 24);
			this.mnuShape.TabIndex = 1;
			this.mnuShape.Text = "mnuShape";
			this.mnuShape.Visible = false;
			// 
			// mnuImage
			// 
			this.mnuImage.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.mnuImageSelect,
            this.mnuImageSelectAll,
            mnuImageDiv1,
            this.mnuImagePaint,
            this.mnuImageRadius,
            this.mnuImageWeight,
            this.falloff00ToolStripMenuItem,
            mnuImageDiv2,
            this.mnuImageCut,
            this.mnuImageCopy,
            this.mnuImagePaste,
            mnuImageDiv3,
            this.mnuImageClear});
			this.mnuImage.MergeAction = System.Windows.Forms.MergeAction.Insert;
			this.mnuImage.MergeIndex = 2;
			this.mnuImage.Name = "mnuImage";
			this.mnuImage.Size = new System.Drawing.Size(49, 20);
			this.mnuImage.Text = "&Image";
			// 
			// mnuImageSelect
			// 
			this.mnuImageSelect.Name = "mnuImageSelect";
			this.mnuImageSelect.ShortcutKeyDisplayString = "S";
			this.mnuImageSelect.Size = new System.Drawing.Size(150, 22);
			this.mnuImageSelect.Text = "&Select";
			// 
			// mnuImageSelectAll
			// 
			this.mnuImageSelectAll.Name = "mnuImageSelectAll";
			this.mnuImageSelectAll.ShortcutKeyDisplayString = "A";
			this.mnuImageSelectAll.Size = new System.Drawing.Size(150, 22);
			this.mnuImageSelectAll.Text = "Select &All";
			// 
			// mnuImagePaint
			// 
			this.mnuImagePaint.Name = "mnuImagePaint";
			this.mnuImagePaint.ShortcutKeyDisplayString = "P";
			this.mnuImagePaint.Size = new System.Drawing.Size(150, 22);
			this.mnuImagePaint.Text = "&Paint";
			// 
			// mnuImageRadius
			// 
			this.mnuImageRadius.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.toolStripMenuItem3,
            this.toolStripMenuItem4,
            this.toolStripMenuItem5,
            this.toolStripMenuItem7,
            this.toolStripMenuItem8,
            this.toolStripMenuItem2,
            this.toolStripMenuItem10,
            this.toolStripMenuItem11});
			this.mnuImageRadius.Name = "mnuImageRadius";
			this.mnuImageRadius.Size = new System.Drawing.Size(150, 22);
			this.mnuImageRadius.Text = "&Radius (8)";
			// 
			// toolStripMenuItem3
			// 
			this.toolStripMenuItem3.Name = "toolStripMenuItem3";
			this.toolStripMenuItem3.ShortcutKeyDisplayString = "1";
			this.toolStripMenuItem3.Size = new System.Drawing.Size(142, 22);
			this.toolStripMenuItem3.Text = "1";
			// 
			// toolStripMenuItem4
			// 
			this.toolStripMenuItem4.Name = "toolStripMenuItem4";
			this.toolStripMenuItem4.ShortcutKeyDisplayString = "2";
			this.toolStripMenuItem4.Size = new System.Drawing.Size(142, 22);
			this.toolStripMenuItem4.Text = "2";
			// 
			// toolStripMenuItem5
			// 
			this.toolStripMenuItem5.Name = "toolStripMenuItem5";
			this.toolStripMenuItem5.ShortcutKeyDisplayString = "3";
			this.toolStripMenuItem5.Size = new System.Drawing.Size(142, 22);
			this.toolStripMenuItem5.Text = "4";
			// 
			// toolStripMenuItem7
			// 
			this.toolStripMenuItem7.Name = "toolStripMenuItem7";
			this.toolStripMenuItem7.ShortcutKeyDisplayString = "4";
			this.toolStripMenuItem7.Size = new System.Drawing.Size(142, 22);
			this.toolStripMenuItem7.Text = "8";
			// 
			// toolStripMenuItem8
			// 
			this.toolStripMenuItem8.Name = "toolStripMenuItem8";
			this.toolStripMenuItem8.ShortcutKeyDisplayString = "5";
			this.toolStripMenuItem8.Size = new System.Drawing.Size(142, 22);
			this.toolStripMenuItem8.Text = "16";
			// 
			// toolStripMenuItem2
			// 
			this.toolStripMenuItem2.Name = "toolStripMenuItem2";
			this.toolStripMenuItem2.Size = new System.Drawing.Size(139, 6);
			// 
			// toolStripMenuItem10
			// 
			this.toolStripMenuItem10.Name = "toolStripMenuItem10";
			this.toolStripMenuItem10.ShortcutKeyDisplayString = "=";
			this.toolStripMenuItem10.Size = new System.Drawing.Size(142, 22);
			this.toolStripMenuItem10.Text = "&Increase";
			// 
			// toolStripMenuItem11
			// 
			this.toolStripMenuItem11.Name = "toolStripMenuItem11";
			this.toolStripMenuItem11.ShortcutKeyDisplayString = "-";
			this.toolStripMenuItem11.Size = new System.Drawing.Size(142, 22);
			this.toolStripMenuItem11.Text = "&Decrease";
			// 
			// mnuImageWeight
			// 
			this.mnuImageWeight.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.toolStripMenuItem12,
            this.toolStripMenuItem13,
            this.toolStripMenuItem14,
            this.toolStripMenuItem15,
            this.toolStripMenuItem16,
            this.toolStripMenuItem9,
            this.increaseToolStripMenuItem,
            this.decreaseToolStripMenuItem});
			this.mnuImageWeight.Name = "mnuImageWeight";
			this.mnuImageWeight.Size = new System.Drawing.Size(150, 22);
			this.mnuImageWeight.Text = "&Weight (1.0)";
			// 
			// toolStripMenuItem12
			// 
			this.toolStripMenuItem12.Name = "toolStripMenuItem12";
			this.toolStripMenuItem12.ShortcutKeyDisplayString = "Q";
			this.toolStripMenuItem12.Size = new System.Drawing.Size(141, 22);
			this.toolStripMenuItem12.Text = "1.0";
			// 
			// toolStripMenuItem13
			// 
			this.toolStripMenuItem13.Name = "toolStripMenuItem13";
			this.toolStripMenuItem13.ShortcutKeyDisplayString = "W";
			this.toolStripMenuItem13.Size = new System.Drawing.Size(141, 22);
			this.toolStripMenuItem13.Text = "0.5";
			// 
			// toolStripMenuItem14
			// 
			this.toolStripMenuItem14.Name = "toolStripMenuItem14";
			this.toolStripMenuItem14.ShortcutKeyDisplayString = "E";
			this.toolStripMenuItem14.Size = new System.Drawing.Size(141, 22);
			this.toolStripMenuItem14.Text = "0.0";
			// 
			// toolStripMenuItem15
			// 
			this.toolStripMenuItem15.Name = "toolStripMenuItem15";
			this.toolStripMenuItem15.ShortcutKeyDisplayString = "R";
			this.toolStripMenuItem15.Size = new System.Drawing.Size(141, 22);
			this.toolStripMenuItem15.Text = "-0.5";
			// 
			// toolStripMenuItem16
			// 
			this.toolStripMenuItem16.Name = "toolStripMenuItem16";
			this.toolStripMenuItem16.ShortcutKeyDisplayString = "T";
			this.toolStripMenuItem16.Size = new System.Drawing.Size(141, 22);
			this.toolStripMenuItem16.Text = "-1.0";
			// 
			// toolStripMenuItem9
			// 
			this.toolStripMenuItem9.Name = "toolStripMenuItem9";
			this.toolStripMenuItem9.Size = new System.Drawing.Size(138, 6);
			// 
			// increaseToolStripMenuItem
			// 
			this.increaseToolStripMenuItem.Name = "increaseToolStripMenuItem";
			this.increaseToolStripMenuItem.ShortcutKeyDisplayString = "]";
			this.increaseToolStripMenuItem.Size = new System.Drawing.Size(141, 22);
			this.increaseToolStripMenuItem.Text = "&Increase";
			// 
			// decreaseToolStripMenuItem
			// 
			this.decreaseToolStripMenuItem.Name = "decreaseToolStripMenuItem";
			this.decreaseToolStripMenuItem.ShortcutKeyDisplayString = "[";
			this.decreaseToolStripMenuItem.Size = new System.Drawing.Size(141, 22);
			this.decreaseToolStripMenuItem.Text = "&Decrease";
			// 
			// falloff00ToolStripMenuItem
			// 
			this.falloff00ToolStripMenuItem.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.toolStripMenuItem6,
            this.toolStripMenuItem17,
            this.toolStripMenuItem18,
            this.toolStripMenuItem19,
            this.toolStripMenuItem20,
            this.toolStripMenuItem1,
            this.increaseToolStripMenuItem1,
            this.decreaseToolStripMenuItem1});
			this.falloff00ToolStripMenuItem.Name = "falloff00ToolStripMenuItem";
			this.falloff00ToolStripMenuItem.Size = new System.Drawing.Size(150, 22);
			this.falloff00ToolStripMenuItem.Text = "Falloff (0.0)";
			// 
			// toolStripMenuItem6
			// 
			this.toolStripMenuItem6.Name = "toolStripMenuItem6";
			this.toolStripMenuItem6.ShortcutKeyDisplayString = "";
			this.toolStripMenuItem6.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.Q)));
			this.toolStripMenuItem6.Size = new System.Drawing.Size(144, 22);
			this.toolStripMenuItem6.Text = "1.0";
			// 
			// toolStripMenuItem17
			// 
			this.toolStripMenuItem17.Name = "toolStripMenuItem17";
			this.toolStripMenuItem17.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.W)));
			this.toolStripMenuItem17.Size = new System.Drawing.Size(144, 22);
			this.toolStripMenuItem17.Text = "0.5";
			// 
			// toolStripMenuItem18
			// 
			this.toolStripMenuItem18.Name = "toolStripMenuItem18";
			this.toolStripMenuItem18.ShortcutKeyDisplayString = "";
			this.toolStripMenuItem18.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.E)));
			this.toolStripMenuItem18.Size = new System.Drawing.Size(144, 22);
			this.toolStripMenuItem18.Text = "0.0";
			// 
			// toolStripMenuItem19
			// 
			this.toolStripMenuItem19.Name = "toolStripMenuItem19";
			this.toolStripMenuItem19.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.R)));
			this.toolStripMenuItem19.Size = new System.Drawing.Size(144, 22);
			this.toolStripMenuItem19.Text = "-0.5";
			// 
			// toolStripMenuItem20
			// 
			this.toolStripMenuItem20.Name = "toolStripMenuItem20";
			this.toolStripMenuItem20.ShortcutKeyDisplayString = "";
			this.toolStripMenuItem20.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.T)));
			this.toolStripMenuItem20.Size = new System.Drawing.Size(144, 22);
			this.toolStripMenuItem20.Text = "-1.0";
			// 
			// toolStripMenuItem1
			// 
			this.toolStripMenuItem1.Name = "toolStripMenuItem1";
			this.toolStripMenuItem1.Size = new System.Drawing.Size(141, 6);
			// 
			// increaseToolStripMenuItem1
			// 
			this.increaseToolStripMenuItem1.Name = "increaseToolStripMenuItem1";
			this.increaseToolStripMenuItem1.ShortcutKeyDisplayString = "}";
			this.increaseToolStripMenuItem1.Size = new System.Drawing.Size(144, 22);
			this.increaseToolStripMenuItem1.Text = "Increase";
			// 
			// decreaseToolStripMenuItem1
			// 
			this.decreaseToolStripMenuItem1.Name = "decreaseToolStripMenuItem1";
			this.decreaseToolStripMenuItem1.ShortcutKeyDisplayString = "{";
			this.decreaseToolStripMenuItem1.Size = new System.Drawing.Size(144, 22);
			this.decreaseToolStripMenuItem1.Text = "Decrease";
			// 
			// mnuImageCut
			// 
			this.mnuImageCut.Name = "mnuImageCut";
			this.mnuImageCut.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.X)));
			this.mnuImageCut.Size = new System.Drawing.Size(150, 22);
			this.mnuImageCut.Text = "Cu&t";
			// 
			// mnuImageCopy
			// 
			this.mnuImageCopy.Name = "mnuImageCopy";
			this.mnuImageCopy.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.C)));
			this.mnuImageCopy.Size = new System.Drawing.Size(150, 22);
			this.mnuImageCopy.Text = "&Copy";
			// 
			// mnuImagePaste
			// 
			this.mnuImagePaste.Name = "mnuImagePaste";
			this.mnuImagePaste.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.V)));
			this.mnuImagePaste.Size = new System.Drawing.Size(150, 22);
			this.mnuImagePaste.Text = "&Paste";
			// 
			// mnuImageClear
			// 
			this.mnuImageClear.Name = "mnuImageClear";
			this.mnuImageClear.ShortcutKeys = System.Windows.Forms.Keys.Delete;
			this.mnuImageClear.Size = new System.Drawing.Size(150, 22);
			this.mnuImageClear.Text = "&Clear";
			// 
			// areaToolStripMenuItem
			// 
			this.areaToolStripMenuItem.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.selectToolStripMenuItem,
            this.selectAllToolStripMenuItem,
            this.toolStripMenuItem21,
            this.addToolStripMenuItem,
            this.deleteToolStripMenuItem,
            this.toolStripMenuItem22});
			this.areaToolStripMenuItem.MergeIndex = 3;
			this.areaToolStripMenuItem.Name = "areaToolStripMenuItem";
			this.areaToolStripMenuItem.Size = new System.Drawing.Size(43, 20);
			this.areaToolStripMenuItem.Text = "&Zone";
			// 
			// selectToolStripMenuItem
			// 
			this.selectToolStripMenuItem.Name = "selectToolStripMenuItem";
			this.selectToolStripMenuItem.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.S)));
			this.selectToolStripMenuItem.Size = new System.Drawing.Size(167, 22);
			this.selectToolStripMenuItem.Text = "&Select";
			// 
			// selectAllToolStripMenuItem
			// 
			this.selectAllToolStripMenuItem.Name = "selectAllToolStripMenuItem";
			this.selectAllToolStripMenuItem.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.A)));
			this.selectAllToolStripMenuItem.Size = new System.Drawing.Size(167, 22);
			this.selectAllToolStripMenuItem.Text = "Select &All";
			// 
			// toolStripMenuItem21
			// 
			this.toolStripMenuItem21.Name = "toolStripMenuItem21";
			this.toolStripMenuItem21.Size = new System.Drawing.Size(164, 6);
			// 
			// addToolStripMenuItem
			// 
			this.addToolStripMenuItem.Name = "addToolStripMenuItem";
			this.addToolStripMenuItem.Size = new System.Drawing.Size(167, 22);
			this.addToolStripMenuItem.Text = "Add";
			// 
			// deleteToolStripMenuItem
			// 
			this.deleteToolStripMenuItem.Name = "deleteToolStripMenuItem";
			this.deleteToolStripMenuItem.Size = new System.Drawing.Size(167, 22);
			this.deleteToolStripMenuItem.Text = "Delete";
			// 
			// toolStripMenuItem22
			// 
			this.toolStripMenuItem22.Name = "toolStripMenuItem22";
			this.toolStripMenuItem22.Size = new System.Drawing.Size(164, 6);
			// 
			// tbrShape
			// 
			this.tbrShape.Items.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.toolStripButton1});
			this.tbrShape.Location = new System.Drawing.Point(0, 0);
			this.tbrShape.Name = "tbrShape";
			this.tbrShape.Size = new System.Drawing.Size(300, 25);
			this.tbrShape.TabIndex = 2;
			this.tbrShape.Text = "toolStrip1";
			this.tbrShape.Visible = false;
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
			// frmShape
			// 
			this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
			this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
			this.ClientSize = new System.Drawing.Size(300, 324);
			this.Controls.Add(this.mnuShape);
			this.Controls.Add(this.tbrShape);
			this.Controls.Add(this.picShape);
			this.Font = new System.Drawing.Font("Tahoma", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
			this.MainMenuStrip = this.mnuShape;
			this.Name = "frmShape";
			this.Text = "Shape";
			this.FormClosed += new System.Windows.Forms.FormClosedEventHandler(this.frmShape_FormClosed);
			this.Load += new System.EventHandler(this.Shape_Load);
			((System.ComponentModel.ISupportInitialize)(this.picShape)).EndInit();
			this.mnuShape.ResumeLayout(false);
			this.mnuShape.PerformLayout();
			this.tbrShape.ResumeLayout(false);
			this.tbrShape.PerformLayout();
			this.ResumeLayout(false);
			this.PerformLayout();

		}

		#endregion

		private System.Windows.Forms.PictureBox picShape;
		private System.Windows.Forms.MenuStrip mnuShape;
		private System.Windows.Forms.ToolStripMenuItem mnuImage;
		private System.Windows.Forms.ToolStripMenuItem mnuImageClear;
		private System.Windows.Forms.ToolStripMenuItem mnuImageCut;
		private System.Windows.Forms.ToolStripMenuItem mnuImageCopy;
		private System.Windows.Forms.ToolStripMenuItem mnuImagePaste;
		private System.Windows.Forms.ToolStripButton toolStripButton1;
		public System.Windows.Forms.ToolStrip tbrShape;
		private System.Windows.Forms.ToolStripMenuItem mnuImagePaint;
		private System.Windows.Forms.ToolStripMenuItem mnuImageRadius;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem3;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem4;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem5;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem7;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem8;
		private System.Windows.Forms.ToolStripSeparator toolStripMenuItem2;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem10;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem11;
		private System.Windows.Forms.ToolStripMenuItem mnuImageWeight;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem12;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem13;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem14;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem15;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem16;
		private System.Windows.Forms.ToolStripSeparator toolStripMenuItem9;
		private System.Windows.Forms.ToolStripMenuItem increaseToolStripMenuItem;
		private System.Windows.Forms.ToolStripMenuItem decreaseToolStripMenuItem;
		private System.Windows.Forms.ToolStripMenuItem mnuImageSelect;
		private System.Windows.Forms.ToolStripMenuItem mnuImageSelectAll;
		private System.Windows.Forms.ToolStripMenuItem falloff00ToolStripMenuItem;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem6;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem17;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem18;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem19;
		private System.Windows.Forms.ToolStripMenuItem toolStripMenuItem20;
		private System.Windows.Forms.ToolStripSeparator toolStripMenuItem1;
		private System.Windows.Forms.ToolStripMenuItem increaseToolStripMenuItem1;
		private System.Windows.Forms.ToolStripMenuItem decreaseToolStripMenuItem1;
		private System.Windows.Forms.ToolStripMenuItem areaToolStripMenuItem;
		private System.Windows.Forms.ToolStripMenuItem selectToolStripMenuItem;
		private System.Windows.Forms.ToolStripMenuItem selectAllToolStripMenuItem;
		private System.Windows.Forms.ToolStripSeparator toolStripMenuItem21;
		private System.Windows.Forms.ToolStripMenuItem addToolStripMenuItem;
		private System.Windows.Forms.ToolStripMenuItem deleteToolStripMenuItem;
		private System.Windows.Forms.ToolStripSeparator toolStripMenuItem22;
	}
}