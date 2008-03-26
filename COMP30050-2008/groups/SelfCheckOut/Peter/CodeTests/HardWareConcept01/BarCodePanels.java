	/**
	 * This  class is used to ............... for the Hardware interface 
	 * components of the SelfChekcOut project.
	 * <p>
	 * 
	 * @author Peter Gibney
	 * @version 23rd March 2008.
	 */
import java.awt.*;
import java.util.Random;
import javax.swing.*;
import java.awt.image.*;
import java.text.DecimalFormat;
import javax.media.*;
import javax.media.format.VideoFormat;
import javax.media.util.BufferToImage;


class BarCodePanels extends JPanel implements Runnable {
	
	private static final int DELAY = 50; // ms 

	private CameraCapture camera = null;
	private Decoder decoder = null;
	private boolean stopRequested = false;

	// used for the average ms snap time info
	private int imageCount = 0;
	private long totalTime = 0;
	private DecimalFormat decimalFormat;
	private Font msgFont;
	private Color blackColor = new Color(0, 0, 0);
	private Color whiteColor = new Color(255, 255, 255);

	private BufferedImage imageGrey = new BufferedImage(640, 480,
			BufferedImage.TYPE_BYTE_GRAY);

	BufferedImage imageBinary = new BufferedImage(640, 480,
			BufferedImage.TYPE_BYTE_BINARY);

	private BufferedImage imageColour = new BufferedImage(640, 480,
			BufferedImage.TYPE_INT_RGB);

	BarCodeDeCoder deCoder = new BarCodeDeCoder();

	Graphics2D graphicBinary = imageBinary.createGraphics();
	Graphics2D graphicColour = imageColour.createGraphics();
	Graphics2D graphicGrey = imageGrey.createGraphics();
	
	Barcode code = null; //the decoded barcode
	private ScalesAndBarCode myScalesAndBarCode = null;
	private WeightAndCode myWeightAndCode = null;
	
	private volatile boolean latestScreenDrawn = false; //true; // assume screen is drawn and we are ready to compute new data
	private boolean drawMainPic = true;
	private boolean drawGreyPic = true;
	private boolean drawBinaryPic = true;
	
	private Random laserLine = new Random();
	
	private int blackRGB = blackColor.getRGB();
	private int whiteRGB = whiteColor.getRGB();

	// ------------------------------------------------------
	public BarCodePanels() {
		camera = new CameraCapture();
		decoder = new Decoder();
		Dimension dim = Toolkit.getDefaultToolkit().getScreenSize();
		System.out.println("dim.height = " + dim.height + " dim.width = "
				+ dim.width);
		setBackground(Color.white);
		Dimension d = new Dimension(2 * HWIconst.CAM_SIZE_X, 2 * HWIconst.CAM_SIZE_Y);
		setMinimumSize(d);
		setPreferredSize(d);
		decimalFormat = new DecimalFormat("#0.#"); // 1 decimal place
		msgFont = new Font("SansSerif", Font.BOLD, 15);
		myScalesAndBarCode = new ScalesAndBarCode();
		myScalesAndBarCode.start();
		decoder = new Decoder();
		decoder.start();
		new Thread(this).start(); // start updating the panel's image
	} // end of BarCodePanels()
	// ------------------------------------------------------
	private BufferedImage makeGrey(BufferedImage inImage) {
		assert inImage != null;
		// Graphics2D graphicGrey = imageGrey.createGraphics();
		graphicGrey.drawImage(inImage, 0, 0, null);
		// graphicBinary.dispose();
		return imageGrey;
	}
	// ------------------------------------------------------
	private int[][] makeCompImage(BufferedImage inImage) {
		assert inImage != null;
		int sizeX = inImage.getWidth();
		int sizeY = inImage.getHeight();
		sizeX = 200;
		sizeY = 200;
		int[][] ScanScope = new int[sizeY][sizeX]; // Declares, 2-dim array for screen grab processing. 
		for (int x = 0; x < sizeX; x++) {
			int pixel = inImage.getRGB(x, x);
			ScanScope[x][x] = pixel;
		}
		return ScanScope;
	}
	// ------------------------------------------------------
	private boolean sameImages(int[][] inPut1, int[][] inPut2) {
		assert inPut1 != null;
		assert inPut2 != null;
		for (int x = 0; x < 200/*640*/; x++) {
			if ((inPut1[x][x]) != (inPut2[x][x])) //y,x
				return false;
		}
		return true;
	}
	// ------------------------------------------------------	
	private BufferedImage makeBinary(BufferedImage inImage) {
		assert inImage != null;
		// System.out.println("inImage.getWidth() = " + inImage.getWidth() + ", inImage.getHeight() = " + inImage.getHeight());
		// Graphics2D graphicBinary = imageBinary.createGraphics();
		graphicBinary.drawImage(inImage, 0, 0, null);
		// graphicBinary.dispose();
		return imageBinary;
	}
	//------------------------------------------------------
	private BufferedImage makeAltBinary(BufferedImage inImage) {
		assert inImage != null;
		//System.out.println("inImage.getWidth() = " + inImage.getWidth() + ", inImage.getHeight() = " + inImage.getHeight());
		BufferedImage binary = new BufferedImage(inImage.getWidth(), 
											inImage.getHeight(), 
											BufferedImage.TYPE_INT_RGB);
											// BufferedImage.TYPE_3BYTE_BGR);
		
		int X_size = binary.getWidth();
		int Y_size = binary.getHeight();
		
		
		int totalPixVals = 0;
		for (int x=0;x<X_size;x++){
			for (int y=0;y<Y_size;y++){
				int pixel = inImage.getRGB(x, y);
				Color pixelColour = new Color(pixel, false);
				int greyCol = (pixelColour.getBlue());
				greyCol = greyCol + pixelColour.getRed();
				greyCol = greyCol + pixelColour.getGreen();
				greyCol = greyCol/3;
				totalPixVals = totalPixVals + greyCol;
			}
		}
		int avgPixVals = totalPixVals/(X_size*Y_size);
		
		for (int x=0+10;x<X_size-10;x++){ //note clipping out 10 pix from the sides
			for (int y=0+10;y<Y_size-10;y++){
				int pixel = inImage.getRGB(x, y);
				Color pixelColour = new Color(pixel, false);
				int greyCol = (pixelColour.getBlue());
				greyCol = greyCol + pixelColour.getRed();
				greyCol = greyCol + pixelColour.getGreen();
				greyCol = greyCol/3;

				//if (greyCol < (AverageVals[y][x])) {
				if (greyCol < (avgPixVals + 20)) {
					binary.setRGB(x, y, blackRGB);
				}else {
					binary.setRGB(x, y, whiteRGB);
				}
			}
		}
		//System.out.println("copy.getWidth() = " + copy.getWidth() + ", copy.getHeight() = " + copy.getHeight());
		return binary;
	}
//---------------------------------------------
	private BufferedImage messWith(BufferedImage inImage) {
		Graphics2D graphBin = inImage.createGraphics();
		graphBin.drawImage(inImage, 0, 0, null);
		graphBin.setFont(new Font("Helvetica",Font.BOLD,12));
		graphBin.drawString("Testing....", 5, 14);
		return inImage;
	}
//---------------------------------------------------
	
	public void run(){
	/* take a picture every DELAY ms */
		System.out.println("At start of BarCodePanels.run()");
		long duration = 0;
		BufferedImage im = null;
		int modifyImage = 15;
		Image rawImage = null;
		
		int[][] inImage1 = null;
		int[][] inImage2 = null;
		int sameCnt = 0;
		int totCnt = 0;
		synchronized(this) {
			myWeightAndCode = myScalesAndBarCode.getWeightsAndCode();
			code = new Barcode("1234567890123");
		}
		BufferToImage bufferToImage = null;
		Buffer grabbedFrame = null;
		grabbedFrame = camera.grabFrame();
		if (grabbedFrame == null) {
			System.out.println("No direct grabbed buffer");
		} else {
			// there is a buffer, but check if it's empty or not
			VideoFormat vf = (VideoFormat) grabbedFrame.getFormat();
			if (vf == null) {
				System.out.println("No video format in  direct grabbed buffer");
			} else {
				System.out.println("Direct Grabbed Video format: " + vf);
				bufferToImage = new BufferToImage(vf);
			}
		}
		
		if (bufferToImage == null) {
			System.out.println("bufferToImage == null: ");
		}
		
		grabbedFrame = camera.grabFrame();
		if (grabbedFrame == null) {
			System.out.println("No direcgt grabbed buffer");
		} else {
			
		}
		rawImage = bufferToImage.createImage(grabbedFrame);
		graphicColour.drawImage(rawImage, 0, 0, null);
		inImage1 = makeCompImage(imageColour);
		inImage2 = makeCompImage(imageColour);
		
		while (!stopRequested()) {
			synchronized(this) {
				while (!latestScreenDrawn) { // wait until the last info is drawn
					try {
						wait();
					} 	catch (InterruptedException e) { 
						System.out.println("BarCodePanels() interrupted exception");
						e.printStackTrace();
					} // ignore the exception
				}
				assert Thread.holdsLock(this);
				assert Thread.currentThread().holdsLock(this);
				if (HWIconst.SHOW_INTER_LEAVING)
					System.out.print("(");
				long startTime = System.currentTimeMillis();
				
				grabbedFrame = camera.grabFrame();
				if (grabbedFrame == null) {
					System.out.println("No direct grabbed buffer");
					duration = System.currentTimeMillis() - startTime;
					duration = Math.max(duration,17);
					totalTime += duration;
				} else {
					rawImage = bufferToImage.createImage(grabbedFrame);
					long pre = System.currentTimeMillis();
					myWeightAndCode = myScalesAndBarCode.getWeightsAndCode();
					long post = System.currentTimeMillis();
					System.out.println("dur= " + duration + ", Sleep= " + (DELAY - duration));
				
					int sameThreshold = 0;
				
					if (rawImage == null) {
						// if (im == null) {
						System.out.println("Problem loading image " + (imageCount + 1));
						duration = System.currentTimeMillis() - startTime;
						duration = Math.max(duration,17);
						totalTime += duration;
						modifyImage++;
					} else {
						System.out.println(".");
						graphicColour.drawImage(rawImage, 0, 0, null);
						// Overlay current time on top of the image
						graphicColour.setColor(Color.RED);
						graphicColour.setFont(new Font("Helvetica",Font.BOLD,12));
						graphicColour.drawString(HWIHelper.padIntToString(modifyImage, 6), 5, 14);
						imageCount++;
						decoder.determineCode(imageCount);
						if (modifyImage >= HWIconst.ELAPSED_GRABS) {
							imageGrey = makeGrey(imageColour); // make the grey image
							//imageBinary = makeBinary(imageColour); // make the binary image
							//imageBinary = makeAltBinary(imageColour); // make the binary image
							imageBinary = makeBinary(imageColour); // make the binary image
							//System.out.println("Same count = " + sameCnt + ", out of " + totCnt);
							sameCnt = 0;
							totCnt = 0;
							myWeightAndCode = myScalesAndBarCode.getWeightsAndCode();
							graphicColour.drawString(HWIHelper.padIntToString(modifyImage, 6), 5, 14);
							code = deCoder.getCode(imageBinary);
							System.out.println("Code = " + code);
							imageBinary = messWith(imageBinary);
							//graphicBinary.drawImage(imageBinary, 0, 0, null);
							//graphicBinary.setFont(new Font("Helvetica",Font.BOLD,12));
							//graphicBinary.drawString(code.toString(), 5, 14);
							modifyImage = 0;
							// repaint();
							drawGreyPic = true; //going to need to refresh the grey picture
							drawBinaryPic = true; //going to need to refresh the binary picture
						} else {
							drawGreyPic = false; //not going to need to refresh the grey picture
							drawBinaryPic = false; //not going to need to refresh the binary picture
						}
						modifyImage++;
						duration = System.currentTimeMillis() - startTime;
						totalTime += duration;
						System.out.print(" D ");
						latestScreenDrawn = false; //going to need an update to the screen
						notifyAll();
						repaint();
					}
				}	
					if (HWIconst.SHOW_INTER_LEAVING)
						System.out.print(")");
			} // release  sync
			
			System.out.println("Sleeping for : " + (DELAY - duration));
			if (duration < DELAY) {
				try {
					Thread.sleep(DELAY - duration); // wait until DELAY time has passed
					//System.out.println("Sleeping for : " + (DELAY - duration));
				} catch (Exception ex) {
					System.out.println("BarCodePanels() exception = " + ex.toString());
					ex.printStackTrace();
				}
				
			}
		}
	} // end of run()
	// ------------------------------------------------------
	public void paintComponent(Graphics g) {
		assert g != null;
	/* Draw the snap and add the average ms snap time at the 
	 bottom of the panel. */
		
		synchronized(this) {
			assert Thread.holdsLock(this);
			assert Thread.currentThread().holdsLock(this);
			// make sure that we have finisehd modifying adn readig the camera/barcode fields
			while (latestScreenDrawn) {
				try {
					wait();
				}
				catch (InterruptedException e) { 
					System.out.println("BarCodePanels() interrupted exception");
					e.printStackTrace();
				}
			}
			if (HWIconst.SHOW_INTER_LEAVING)
				System.out.print("{");
			
			//imageColour = deCoder.messWith(imageColour);
			g.drawImage(imageColour, 0, 0, this); // draw the snap
			g.setColor(Color.red);
			int laserPos = 220 + laserLine.nextInt(29);
			g.drawLine(0, laserPos, 640, laserPos);
			
			if (drawGreyPic) {
				//imageGrey = deCoder.messWith(imageGrey);
				g.drawImage(imageGrey, 640, 0, this); // draw the snap
			}
			if (drawBinaryPic) {
				g.drawImage(imageBinary, 0, 480, this); // draw the snap
				// write stats
				
				for (int i = 0; i < 480; i++) {
					if (deCoder.hasSomeCode(i)) {
						if (deCoder.hasFullCode(i)) {
							g.setColor(Color.green);
						} else {
							g.setColor(Color.blue);
						}
						g.drawLine(deCoder.getStartCol(i) + 640, i, deCoder
								.getStopCol(i) + 640, i);
					}
				}
			}
			
			
			g.clearRect(640, 480, 640, 480);
			g.setColor(Color.blue);
			g.setFont(msgFont);
			if (imageCount > 0) {
				double avgGrabTime = (double) totalTime / imageCount;
				g.drawString("Grab " + HWIHelper.padIntToString(imageCount, 5) + 
										", average time per grab =  " + 
										decimalFormat.format(avgGrabTime) +
										" ms" + " from decoder =" + HWIHelper.padIntToString(decoder.getResult(),6), 690, 500);
				g.drawString("Code = " + code , 690, 550);
				
				if (myWeightAndCode != null) { 
					g.drawString("Weight 1 = " + 
						HWIHelper.padIntToString(myWeightAndCode.getWeight(1),4)
						, 690, 590);
					g.drawString("Weight 2 = " +  
						HWIHelper.padIntToString(myWeightAndCode.getWeight(2),4)
						, 690, 630);
					g.drawString("Code = " + 
						HWIHelper.padIntToString(myWeightAndCode.getCode(), 4)
						, 690, 670);
				}
			} else {
				// no image yet
			}
			if (HWIconst.SHOW_INTER_LEAVING)
				System.out.print("}");
			latestScreenDrawn = true;
			// Notify data modifier that we have finished reading the data, now safe to modify data.
			notifyAll();
		}
	} // end of paintComponent()
	// ------------------------------------------------------
	private synchronized boolean stopRequested() {
		return stopRequested;
	}	
	// ------------------------------------------------------	
	public void closeDown() {
	/* Terminate run() and wait for the camera to be closed.
	 This prevents exiting until everything
	 has finished. */
		synchronized (this) {
			stopRequested = true;
			camera.close(); // close down the camera
			myScalesAndBarCode.done();
			decoder.done();
		} //end sync
		while (!camera.isClosed() || !myScalesAndBarCode.isStopped()|| !decoder.isStopped()) {
			if (HWIconst.DE_BUG_THREAD_SHUT_DOWN) {
				System.out.println("in BarCodePanels.closeDown(), waiting:");
				System.out.println("        camera.isClosed() : " + 
						camera.isClosed());
				System.out.println("        myScalesAndBarCode.isClosed() : " + 
						myScalesAndBarCode.isStopped());
				System.out.println("        decoder.isClosed() : " + 
						decoder.isStopped());
			}
			try {
				Thread.sleep(DELAY);
			} catch (Exception ex) {
				System.out.println("BarCodePanels() exception = " + ex.toString());
				ex.printStackTrace();
			}
		}
	} // end of closeDown()
}
