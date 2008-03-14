namespace Shed
{
	partial class frmShed
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
			System.ComponentModel.ComponentResourceManager resources = new System.ComponentModel.ComponentResourceManager(typeof(frmShed));
			this.mnuShed = new System.Windows.Forms.MenuStrip();
			this.mnuFile = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuFileOpen = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuFileSave = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuFileSaveAs = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuFileCompile = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuFileExit = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuShape = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuShapeNew = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuShapeNewChild = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuShapeDelete = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuWindow = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuWindowArrange = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuWindowCascade = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuWindowHorizontal = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuWindowVertical = new System.Windows.Forms.ToolStripMenuItem();
			this.mnuWindowCloseAll = new System.Windows.Forms.ToolStripMenuItem();
			this.stsShed = new System.Windows.Forms.StatusStrip();
			this.stsStatus = new System.Windows.Forms.ToolStripStatusLabel();
			this.tbrShed = new System.Windows.Forms.ToolStrip();
			this.splPropertiesSplit = new System.Windows.Forms.Splitter();
			this.spcProperties = new System.Windows.Forms.SplitContainer();
			this.tvwShapes = new System.Windows.Forms.TreeView();
			this.imlShed = new System.Windows.Forms.ImageList(this.components);
			this.pgdProperties = new System.Windows.Forms.PropertyGrid();
			this.splProperties = new System.Windows.Forms.Splitter();
			this.dlgOpen = new System.Windows.Forms.OpenFileDialog();
			this.dlgSave = new System.Windows.Forms.SaveFileDialog();
			this.dlgCompile = new System.Windows.Forms.FolderBrowserDialog();
			mnuFileDiv1 = new System.Windows.Forms.ToolStripSeparator();
			mnuFileDiv2 = new System.Windows.Forms.ToolStripSeparator();
			this.mnuShed.SuspendLayout();
			this.stsShed.SuspendLayout();
			this.spcProperties.Panel1.SuspendLayout();
			this.spcProperties.Panel2.SuspendLayout();
			this.spcProperties.SuspendLayout();
			this.SuspendLayout();
			// 
			// mnuFileDiv1
			// 
			mnuFileDiv1.Name = "mnuFileDiv1";
			mnuFileDiv1.Size = new System.Drawing.Size(133, 6);
			// 
			// mnuFileDiv2
			// 
			mnuFileDiv2.Name = "mnuFileDiv2";
			mnuFileDiv2.Size = new System.Drawing.Size(133, 6);
			// 
			// mnuShed
			// 
			this.mnuShed.Items.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.mnuFile,
            this.mnuShape,
            this.mnuWindow});
			this.mnuShed.Location = new System.Drawing.Point(0, 0);
			this.mnuShed.MdiWindowListItem = this.mnuWindow;
			this.mnuShed.Name = "mnuShed";
			this.mnuShed.Size = new System.Drawing.Size(922, 24);
			this.mnuShed.TabIndex = 1;
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
			this.mnuFileOpen.Size = new System.Drawing.Size(136, 22);
			this.mnuFileOpen.Text = "&Open...";
			this.mnuFileOpen.Click += new System.EventHandler(this.mnuFileOpen_Click);
			// 
			// mnuFileSave
			// 
			this.mnuFileSave.Name = "mnuFileSave";
			this.mnuFileSave.Size = new System.Drawing.Size(136, 22);
			this.mnuFileSave.Text = "&Save";
			this.mnuFileSave.Click += new System.EventHandler(this.mnuFileSave_Click);
			// 
			// mnuFileSaveAs
			// 
			this.mnuFileSaveAs.Name = "mnuFileSaveAs";
			this.mnuFileSaveAs.Size = new System.Drawing.Size(136, 22);
			this.mnuFileSaveAs.Text = "Save &As...";
			this.mnuFileSaveAs.Click += new System.EventHandler(this.mnuFileSaveAs_Click);
			// 
			// mnuFileCompile
			// 
			this.mnuFileCompile.Name = "mnuFileCompile";
			this.mnuFileCompile.Size = new System.Drawing.Size(136, 22);
			this.mnuFileCompile.Text = "&Compile";
			this.mnuFileCompile.Click += new System.EventHandler(this.mnuFileCompile_Click);
			// 
			// mnuFileExit
			// 
			this.mnuFileExit.Name = "mnuFileExit";
			this.mnuFileExit.Size = new System.Drawing.Size(136, 22);
			this.mnuFileExit.Text = "E&xit";
			this.mnuFileExit.Click += new System.EventHandler(this.exitToolStripMenuItem_Click);
			// 
			// mnuShape
			// 
			this.mnuShape.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.mnuShapeNew,
            this.mnuShapeNewChild,
            this.mnuShapeDelete});
			this.mnuShape.MergeIndex = 1;
			this.mnuShape.Name = "mnuShape";
			this.mnuShape.Size = new System.Drawing.Size(49, 20);
			this.mnuShape.Text = "&Shape";
			// 
			// mnuShapeNew
			// 
			this.mnuShapeNew.Name = "mnuShapeNew";
			this.mnuShapeNew.Size = new System.Drawing.Size(132, 22);
			this.mnuShapeNew.Text = "&New";
			this.mnuShapeNew.Click += new System.EventHandler(this.mnuShapeNew_Click);
			// 
			// mnuShapeNewChild
			// 
			this.mnuShapeNewChild.Enabled = false;
			this.mnuShapeNewChild.Name = "mnuShapeNewChild";
			this.mnuShapeNewChild.Size = new System.Drawing.Size(132, 22);
			this.mnuShapeNewChild.Text = "New &Child";
			this.mnuShapeNewChild.Click += new System.EventHandler(this.mnuShapeNewChild_Click);
			// 
			// mnuShapeDelete
			// 
			this.mnuShapeDelete.Name = "mnuShapeDelete";
			this.mnuShapeDelete.Size = new System.Drawing.Size(152, 22);
			this.mnuShapeDelete.Text = "&Delete";
			this.mnuShapeDelete.Click += new System.EventHandler(this.mnuShapeDelete_Click);
			// 
			// mnuWindow
			// 
			this.mnuWindow.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.mnuWindowArrange,
            this.mnuWindowCascade,
            this.mnuWindowHorizontal,
            this.mnuWindowVertical,
            this.mnuWindowCloseAll});
			this.mnuWindow.MergeIndex = 5;
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
			// stsShed
			// 
			this.stsShed.Items.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.stsStatus});
			this.stsShed.Location = new System.Drawing.Point(0, 580);
			this.stsShed.Name = "stsShed";
			this.stsShed.RenderMode = System.Windows.Forms.ToolStripRenderMode.ManagerRenderMode;
			this.stsShed.Size = new System.Drawing.Size(922, 22);
			this.stsShed.TabIndex = 5;
			// 
			// stsStatus
			// 
			this.stsStatus.Name = "stsStatus";
			this.stsStatus.Size = new System.Drawing.Size(42, 17);
			this.stsStatus.Text = "Ready!";
			// 
			// tbrShed
			// 
			this.tbrShed.Location = new System.Drawing.Point(0, 24);
			this.tbrShed.Name = "tbrShed";
			this.tbrShed.Size = new System.Drawing.Size(473, 25);
			this.tbrShed.TabIndex = 9;
			this.tbrShed.Visible = false;
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
			this.tvwShapes.ImageList = this.imlShed;
			this.tvwShapes.Location = new System.Drawing.Point(0, 0);
			this.tvwShapes.Name = "tvwShapes";
			this.tvwShapes.SelectedImageIndex = 0;
			this.tvwShapes.Size = new System.Drawing.Size(296, 217);
			this.tvwShapes.TabIndex = 0;
			this.tvwShapes.MouseDoubleClick += new System.Windows.Forms.MouseEventHandler(this.tvwShapes_MouseDoubleClick);
			this.tvwShapes.AfterSelect += new System.Windows.Forms.TreeViewEventHandler(this.tvwShapes_AfterSelect);
			// 
			// imlShed
			// 
			this.imlShed.ImageStream = ((System.Windows.Forms.ImageListStreamer)(resources.GetObject("imlShed.ImageStream")));
			this.imlShed.TransparentColor = System.Drawing.Color.Transparent;
			this.imlShed.Images.SetKeyName(0, "Shapes.png");
			this.imlShed.Images.SetKeyName(1, "Shape.png");
			this.imlShed.Images.SetKeyName(2, "Grid.png");
			this.imlShed.Images.SetKeyName(3, "Zone.png");
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
			// dlgOpen
			// 
			this.dlgOpen.DefaultExt = "sap";
			this.dlgOpen.Filter = "Shed Project files|*.sap|All files|*.*";
			this.dlgOpen.Title = "Select the Shed project to open..";
			// 
			// dlgSave
			// 
			this.dlgSave.DefaultExt = "sap";
			this.dlgSave.Filter = "Shed Project files|*.sap|All files|*.*";
			this.dlgSave.Title = "Select a pathname to save the Shed project..";
			// 
			// dlgCompile
			// 
			this.dlgCompile.Description = "Select a folder to store the compiled Shed project and generated .h file";
			this.dlgCompile.RootFolder = System.Environment.SpecialFolder.MyComputer;
			// 
			// frmShed
			// 
			this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
			this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
			this.ClientSize = new System.Drawing.Size(922, 602);
			this.Controls.Add(this.splPropertiesSplit);
			this.Controls.Add(this.spcProperties);
			this.Controls.Add(this.splProperties);
			this.Controls.Add(this.tbrShed);
			this.Controls.Add(this.stsShed);
			this.Controls.Add(this.mnuShed);
			this.Font = new System.Drawing.Font("Tahoma", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
			this.IsMdiContainer = true;
			this.MainMenuStrip = this.mnuShed;
			this.Name = "frmShed";
			this.Text = "Shed (v0.1) - [untitled]";
			this.Resize += new System.EventHandler(this.Shed_Resize);
			this.MdiChildActivate += new System.EventHandler(this.Shed_MdiChildActivate);
			this.FormClosing += new System.Windows.Forms.FormClosingEventHandler(this.frmShed_FormClosing);
			this.Load += new System.EventHandler(this.Shed_Load);
			this.mnuShed.ResumeLayout(false);
			this.mnuShed.PerformLayout();
			this.stsShed.ResumeLayout(false);
			this.stsShed.PerformLayout();
			this.spcProperties.Panel1.ResumeLayout(false);
			this.spcProperties.Panel2.ResumeLayout(false);
			this.spcProperties.ResumeLayout(false);
			this.ResumeLayout(false);
			this.PerformLayout();

		}

		#endregion

		private System.Windows.Forms.MenuStrip mnuShed;
		private System.Windows.Forms.ToolStripMenuItem mnuWindow;
		private System.Windows.Forms.ToolStrip tbrShed;
		private System.Windows.Forms.ToolStripMenuItem mnuFile;
		private System.Windows.Forms.ToolStripMenuItem mnuFileOpen;
		private System.Windows.Forms.ToolStripMenuItem mnuFileSave;
		private System.Windows.Forms.ToolStripMenuItem mnuFileSaveAs;
		private System.Windows.Forms.ToolStripMenuItem mnuFileCompile;
		private System.Windows.Forms.ToolStripMenuItem mnuFileExit;
		private System.Windows.Forms.Splitter splPropertiesSplit;
		private System.Windows.Forms.SplitContainer spcProperties;
		private System.Windows.Forms.TreeView tvwShapes;
		private System.Windows.Forms.Splitter splProperties;
		private System.Windows.Forms.ToolStripMenuItem mnuWindowArrange;
		private System.Windows.Forms.ToolStripMenuItem mnuWindowCascade;
		private System.Windows.Forms.ToolStripMenuItem mnuWindowHorizontal;
		private System.Windows.Forms.ToolStripMenuItem mnuWindowVertical;
		private System.Windows.Forms.ToolStripMenuItem mnuWindowCloseAll;
		private System.Windows.Forms.ToolStripMenuItem mnuShape;
		private System.Windows.Forms.ToolStripMenuItem mnuShapeNew;
		private System.Windows.Forms.ToolStripMenuItem mnuShapeDelete;
		private System.Windows.Forms.ImageList imlShed;
		public System.Windows.Forms.ToolStripStatusLabel stsStatus;
		private System.Windows.Forms.StatusStrip stsShed;
		private System.Windows.Forms.ToolStripMenuItem mnuShapeNewChild;
		private System.Windows.Forms.OpenFileDialog dlgOpen;
		private System.Windows.Forms.SaveFileDialog dlgSave;
		private System.Windows.Forms.FolderBrowserDialog dlgCompile;
		public System.Windows.Forms.PropertyGrid pgdProperties;
	}
}

