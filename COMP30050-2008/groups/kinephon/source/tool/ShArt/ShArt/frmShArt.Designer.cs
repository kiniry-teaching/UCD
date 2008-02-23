namespace ShArt
{
	partial class frmShArt
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
			this.components = new System.ComponentModel.Container();
			System.Windows.Forms.ToolStripSeparator mnuFileDiv1;
			System.Windows.Forms.ToolStripSeparator mnuFileDiv2;
			System.ComponentModel.ComponentResourceManager resources = new System.ComponentModel.ComponentResourceManager(typeof(frmShArt));
			this.mnuShArt = new System.Windows.Forms.MenuStrip();
			this.mnuFile = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuFileOpen = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuFileSave = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuFileSaveAs = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuFileCompile = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuFileExit = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuShape = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuShapeNew = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuShapeDelete = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuWindow = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuWindowArrange = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuWindowCascade = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuWindowHorizontal = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuWindowVertical = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuWindowCloseAll = new System.Windows.Forms.ToolStripMenuItem();
			this.stsShArt = new System.Windows.Forms.StatusStrip();
			this.tbrShArt = new System.Windows.Forms.ToolStrip();
			this.splPropertiesSplit = new System.Windows.Forms.Splitter();
			this.spcProperties = new System.Windows.Forms.SplitContainer();
			this.tvwShapes = new System.Windows.Forms.TreeView();
			this.imlShArt = new System.Windows.Forms.ImageList(this.components);
			this.pgdProperties = new System.Windows.Forms.PropertyGrid();
			this.splProperties = new System.Windows.Forms.Splitter();
			this.stsStatus = new System.Windows.Forms.ToolStripStatusLabel();
			mnuFileDiv1 = new System.Windows.Forms.ToolStripSeparator();
			mnuFileDiv2 = new System.Windows.Forms.ToolStripSeparator();
			this.mnuShArt.SuspendLayout();
			this.stsShArt.SuspendLayout();
			this.spcProperties.Panel1.SuspendLayout();
			this.spcProperties.Panel2.SuspendLayout();
			this.spcProperties.SuspendLayout();
			this.SuspendLayout();
			// 
			// mnuFileDiv1
			// 
			mnuFileDiv1.Name = "mnuFileDiv1";
			mnuFileDiv1.Size = new System.Drawing.Size(149, 6);
			// 
			// mnuFileDiv2
			// 
			mnuFileDiv2.Name = "mnuFileDiv2";
			mnuFileDiv2.Size = new System.Drawing.Size(149, 6);
			// 
			// mnuShArt
			// 
			this.mnuShArt.Items.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.mnuFile,
            this.mnuShape,
            this.mnuWindow});
			this.mnuShArt.Location = new System.Drawing.Point(0, 0);
			this.mnuShArt.MdiWindowListItem = this.mnuWindow;
			this.mnuShArt.Name = "mnuShArt";
			this.mnuShArt.Size = new System.Drawing.Size(922, 24);
			this.mnuShArt.TabIndex = 1;
			// 
			// mnuFile
			// 
			this.mnuFile.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.mnuFileOpen,
            this.mnuFileSave,
            this.mnuFileSaveAs,
            mnuFileDiv1,
            this.mnuFileCompile,
            mnuFileDiv2,
            this.mnuFileExit});
			this.mnuFile.MergeIndex = 0;
			this.mnuFile.Name = "mnuFile";
			this.mnuFile.Size = new System.Drawing.Size(35, 20);
			this.mnuFile.Text = "&File";
			// 
			// mnuFileOpen
			// 
			this.mnuFileOpen.Name = "mnuFileOpen";
			this.mnuFileOpen.Size = new System.Drawing.Size(152, 22);
			this.mnuFileOpen.Text = "&Open...";
			// 
			// mnuFileSave
			// 
			this.mnuFileSave.Name = "mnuFileSave";
			this.mnuFileSave.Size = new System.Drawing.Size(152, 22);
			this.mnuFileSave.Text = "&Save";
			// 
			// mnuFileSaveAs
			// 
			this.mnuFileSaveAs.Name = "mnuFileSaveAs";
			this.mnuFileSaveAs.Size = new System.Drawing.Size(152, 22);
			this.mnuFileSaveAs.Text = "Save &As...";
			// 
			// mnuFileCompile
			// 
			this.mnuFileCompile.Name = "mnuFileCompile";
			this.mnuFileCompile.Size = new System.Drawing.Size(152, 22);
			this.mnuFileCompile.Text = "&Compile";
			// 
			// mnuFileExit
			// 
			this.mnuFileExit.Name = "mnuFileExit";
			this.mnuFileExit.Size = new System.Drawing.Size(152, 22);
			this.mnuFileExit.Text = "E&xit";
			this.mnuFileExit.Click += new System.EventHandler(this.exitToolStripMenuItem_Click);
			// 
			// mnuShape
			// 
			this.mnuShape.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.mnuShapeNew,
            this.mnuShapeDelete});
			this.mnuShape.MergeIndex = 1;
			this.mnuShape.Name = "mnuShape";
			this.mnuShape.Size = new System.Drawing.Size(49, 20);
			this.mnuShape.Text = "&Shape";
			// 
			// mnuShapeNew
			// 
			this.mnuShapeNew.Name = "mnuShapeNew";
			this.mnuShapeNew.Size = new System.Drawing.Size(152, 22);
			this.mnuShapeNew.Text = "&New";
			this.mnuShapeNew.Click += new System.EventHandler(this.mnuShapeNew_Click);
			// 
			// mnuShapeDelete
			// 
			this.mnuShapeDelete.Name = "mnuShapeDelete";
			this.mnuShapeDelete.Size = new System.Drawing.Size(152, 22);
			this.mnuShapeDelete.Text = "&Delete";
			// 
			// mnuWindow
			// 
			this.mnuWindow.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.mnuWindowArrange,
            this.mnuWindowCascade,
            this.mnuWindowHorizontal,
            this.mnuWindowVertical,
            this.mnuWindowCloseAll});
			this.mnuWindow.MergeIndex = 4;
			this.mnuWindow.Name = "mnuWindow";
			this.mnuWindow.Size = new System.Drawing.Size(57, 20);
			this.mnuWindow.Text = "&Window";
			// 
			// mnuWindowArrange
			// 
			this.mnuWindowArrange.Name = "mnuWindowArrange";
			this.mnuWindowArrange.Size = new System.Drawing.Size(160, 22);
			this.mnuWindowArrange.Text = "&Arrange Icons";
			this.mnuWindowArrange.Click += new System.EventHandler(this.mnuWindowArrange_Click);
			// 
			// mnuWindowCascade
			// 
			this.mnuWindowCascade.Name = "mnuWindowCascade";
			this.mnuWindowCascade.Size = new System.Drawing.Size(160, 22);
			this.mnuWindowCascade.Text = "&Cascade";
			this.mnuWindowCascade.Click += new System.EventHandler(this.mnuWindowCascade_Click);
			// 
			// mnuWindowHorizontal
			// 
			this.mnuWindowHorizontal.Name = "mnuWindowHorizontal";
			this.mnuWindowHorizontal.Size = new System.Drawing.Size(160, 22);
			this.mnuWindowHorizontal.Text = "Tile &Horizontally";
			this.mnuWindowHorizontal.Click += new System.EventHandler(this.mnuWindowHorizontal_Click);
			// 
			// mnuWindowVertical
			// 
			this.mnuWindowVertical.Name = "mnuWindowVertical";
			this.mnuWindowVertical.Size = new System.Drawing.Size(160, 22);
			this.mnuWindowVertical.Text = "Tile &Vertically";
			this.mnuWindowVertical.Click += new System.EventHandler(this.mnuWindowVertical_Click);
			// 
			// mnuWindowCloseAll
			// 
			this.mnuWindowCloseAll.Name = "mnuWindowCloseAll";
			this.mnuWindowCloseAll.Size = new System.Drawing.Size(160, 22);
			this.mnuWindowCloseAll.Text = "C&lose All";
			this.mnuWindowCloseAll.Click += new System.EventHandler(this.mnuWindowCloseAll_Click);
			// 
			// stsShArt
			// 
			this.stsShArt.Items.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.stsStatus});
			this.stsShArt.Location = new System.Drawing.Point(0, 580);
			this.stsShArt.Name = "stsShArt";
			this.stsShArt.RenderMode = System.Windows.Forms.ToolStripRenderMode.ManagerRenderMode;
			this.stsShArt.Size = new System.Drawing.Size(922, 22);
			this.stsShArt.TabIndex = 5;
			// 
			// tbrShArt
			// 
			this.tbrShArt.Location = new System.Drawing.Point(0, 24);
			this.tbrShArt.Name = "tbrShArt";
			this.tbrShArt.Size = new System.Drawing.Size(473, 25);
			this.tbrShArt.TabIndex = 9;
			this.tbrShArt.Visible = false;
			// 
			// splPropertiesSplit
			// 
			this.splPropertiesSplit.Dock = System.Windows.Forms.DockStyle.Right;
			this.splPropertiesSplit.Location = new System.Drawing.Point(578, 24);
			this.splPropertiesSplit.Name = "splPropertiesSplit";
			this.splPropertiesSplit.Size = new System.Drawing.Size(4, 556);
			this.splPropertiesSplit.TabIndex = 13;
			this.splPropertiesSplit.TabStop = false;
			this.splPropertiesSplit.SplitterMoved += new System.Windows.Forms.SplitterEventHandler(this.splPropertiesSplit_SplitterMoved);
			// 
			// spcProperties
			// 
			this.spcProperties.Location = new System.Drawing.Point(584, 24);
			this.spcProperties.Name = "spcProperties";
			this.spcProperties.Orientation = System.Windows.Forms.Orientation.Horizontal;
			// 
			// spcProperties.Panel1
			// 
			this.spcProperties.Panel1.Controls.Add(this.tvwShapes);
			// 
			// spcProperties.Panel2
			// 
			this.spcProperties.Panel2.Controls.Add(this.pgdProperties);
			this.spcProperties.Panel2.Resize += new System.EventHandler(this.spcProperties_Panel2_Resize);
			this.spcProperties.Size = new System.Drawing.Size(296, 496);
			this.spcProperties.SplitterDistance = 217;
			this.spcProperties.TabIndex = 12;
			// 
			// tvwShapes
			// 
			this.tvwShapes.Dock = System.Windows.Forms.DockStyle.Fill;
			this.tvwShapes.HideSelection = false;
			this.tvwShapes.ImageIndex = 0;
			this.tvwShapes.ImageList = this.imlShArt;
			this.tvwShapes.Location = new System.Drawing.Point(0, 0);
			this.tvwShapes.Name = "tvwShapes";
			this.tvwShapes.SelectedImageIndex = 0;
			this.tvwShapes.Size = new System.Drawing.Size(296, 217);
			this.tvwShapes.TabIndex = 0;
			this.tvwShapes.MouseDoubleClick += new System.Windows.Forms.MouseEventHandler(this.tvwShapes_MouseDoubleClick);
			this.tvwShapes.AfterSelect += new System.Windows.Forms.TreeViewEventHandler(this.tvwShapes_AfterSelect);
			// 
			// imlShArt
			// 
			this.imlShArt.ImageStream = ((System.Windows.Forms.ImageListStreamer)(resources.GetObject("imlShArt.ImageStream")));
			this.imlShArt.TransparentColor = System.Drawing.Color.Transparent;
			this.imlShArt.Images.SetKeyName(0, "Shapes.png");
			this.imlShArt.Images.SetKeyName(1, "Shape.png");
			this.imlShArt.Images.SetKeyName(2, "Grid.png");
			this.imlShArt.Images.SetKeyName(3, "Zone.png");
			// 
			// pgdProperties
			// 
			this.pgdProperties.Location = new System.Drawing.Point(0, 0);
			this.pgdProperties.Name = "pgdProperties";
			this.pgdProperties.Size = new System.Drawing.Size(144, 104);
			this.pgdProperties.TabIndex = 0;
			// 
			// splProperties
			// 
			this.splProperties.Dock = System.Windows.Forms.DockStyle.Right;
			this.splProperties.Location = new System.Drawing.Point(582, 24);
			this.splProperties.Name = "splProperties";
			this.splProperties.Size = new System.Drawing.Size(340, 556);
			this.splProperties.TabIndex = 11;
			this.splProperties.TabStop = false;
			// 
			// stsStatus
			// 
			this.stsStatus.Name = "stsStatus";
			this.stsStatus.Size = new System.Drawing.Size(42, 17);
			this.stsStatus.Text = "Ready!";
			// 
			// frmShArt
			// 
			this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
			this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
			this.ClientSize = new System.Drawing.Size(922, 602);
			this.Controls.Add(this.splPropertiesSplit);
			this.Controls.Add(this.spcProperties);
			this.Controls.Add(this.splProperties);
			this.Controls.Add(this.tbrShArt);
			this.Controls.Add(this.stsShArt);
			this.Controls.Add(this.mnuShArt);
			this.Font = new System.Drawing.Font("Tahoma", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
			this.IsMdiContainer = true;
			this.MainMenuStrip = this.mnuShArt;
			this.Name = "frmShArt";
			this.Text = "ShArt (v0.1)";
			this.Resize += new System.EventHandler(this.ShArt_Resize);
			this.MdiChildActivate += new System.EventHandler(this.ShArt_MdiChildActivate);
			this.Load += new System.EventHandler(this.ShArt_Load);
			this.mnuShArt.ResumeLayout(false);
			this.mnuShArt.PerformLayout();
			this.stsShArt.ResumeLayout(false);
			this.stsShArt.PerformLayout();
			this.spcProperties.Panel1.ResumeLayout(false);
			this.spcProperties.Panel2.ResumeLayout(false);
			this.spcProperties.ResumeLayout(false);
			this.ResumeLayout(false);
			this.PerformLayout();

		}

		#endregion

		private System.Windows.Forms.MenuStrip mnuShArt;
		private System.Windows.Forms.ToolStripMenuItem mnuWindow;
		private System.Windows.Forms.ToolStrip tbrShArt;
		private System.Windows.Forms.ToolStripMenuItem mnuFile;
		private System.Windows.Forms.ToolStripMenuItem mnuFileOpen;
		private System.Windows.Forms.ToolStripMenuItem mnuFileSave;
		private System.Windows.Forms.ToolStripMenuItem mnuFileSaveAs;
		private System.Windows.Forms.ToolStripMenuItem mnuFileCompile;
		private System.Windows.Forms.ToolStripMenuItem mnuFileExit;
		private System.Windows.Forms.Splitter splPropertiesSplit;
		private System.Windows.Forms.SplitContainer spcProperties;
		private System.Windows.Forms.TreeView tvwShapes;
		private System.Windows.Forms.PropertyGrid pgdProperties;
		private System.Windows.Forms.Splitter splProperties;
		private System.Windows.Forms.ToolStripMenuItem mnuWindowArrange;
		private System.Windows.Forms.ToolStripMenuItem mnuWindowCascade;
		private System.Windows.Forms.ToolStripMenuItem mnuWindowHorizontal;
		private System.Windows.Forms.ToolStripMenuItem mnuWindowVertical;
		private System.Windows.Forms.ToolStripMenuItem mnuWindowCloseAll;
		private System.Windows.Forms.ToolStripMenuItem mnuShape;
		private System.Windows.Forms.ToolStripMenuItem mnuShapeNew;
		private System.Windows.Forms.ToolStripMenuItem mnuShapeDelete;
		private System.Windows.Forms.ImageList imlShArt;
		public System.Windows.Forms.ToolStripStatusLabel stsStatus;
		private System.Windows.Forms.StatusStrip stsShArt;
	}
}

