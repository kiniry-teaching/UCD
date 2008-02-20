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
			this.picShape = new System.Windows.Forms.PictureBox();
			this.menuStrip1 = new System.Windows.Forms.MenuStrip();
			this.imageToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.gridXToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			((System.ComponentModel.ISupportInitialize)(this.picShape)).BeginInit();
			this.menuStrip1.SuspendLayout();
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
			this.menuStrip1.Size = new System.Drawing.Size(57, 24);
			this.menuStrip1.TabIndex = 1;
			this.menuStrip1.Text = "menuStrip1";
			// 
			// imageToolStripMenuItem
			// 
			this.imageToolStripMenuItem.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.gridXToolStripMenuItem});
			this.imageToolStripMenuItem.Name = "imageToolStripMenuItem";
			this.imageToolStripMenuItem.Size = new System.Drawing.Size(49, 20);
			this.imageToolStripMenuItem.Text = "Image";
			// 
			// gridXToolStripMenuItem
			// 
			this.gridXToolStripMenuItem.Name = "gridXToolStripMenuItem";
			this.gridXToolStripMenuItem.Size = new System.Drawing.Size(152, 22);
			this.gridXToolStripMenuItem.Text = "Grid X";
			// 
			// Shape
			// 
			this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
			this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
			this.ClientSize = new System.Drawing.Size(300, 324);
			this.Controls.Add(this.picShape);
			this.Controls.Add(this.menuStrip1);
			this.Font = new System.Drawing.Font("Tahoma", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
			this.MainMenuStrip = this.menuStrip1;
			this.Name = "Shape";
			this.Text = "Shape";
			((System.ComponentModel.ISupportInitialize)(this.picShape)).EndInit();
			this.menuStrip1.ResumeLayout(false);
			this.menuStrip1.PerformLayout();
			this.ResumeLayout(false);
			this.PerformLayout();

		}

		#endregion

		private System.Windows.Forms.PictureBox picShape;
		private System.Windows.Forms.MenuStrip menuStrip1;
		private System.Windows.Forms.ToolStripMenuItem imageToolStripMenuItem;
		private System.Windows.Forms.ToolStripMenuItem gridXToolStripMenuItem;
	}
}