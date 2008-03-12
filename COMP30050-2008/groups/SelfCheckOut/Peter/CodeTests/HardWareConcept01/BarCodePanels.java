import java.awt.*;
import javax.swing.*;
import java.awt.image.*;
import java.text.DecimalFormat;

class BarCodePanels extends JPanel implements Runnable {
	
	
	
	private static final int DELAY = 50; // ms 

	private BufferedImage image = null;
	private BufferedImage greyImage = null;
	private BufferedImage binaryImage = null;
	private CameraCapture camera;
	private boolean running;

	// used for the average ms snap time info
	private int imageCount = 0;
	private long totalTime = 0;
	private DecimalFormat decimalFormat;
	private Font msgFont;
	private Color blackColor = new Color(0, 0, 0);
	private Color whiteColor = new Color(255, 255, 255);

	private BufferedImage grey = new BufferedImage(640, 480,
			BufferedImage.TYPE_BYTE_GRAY);

	BufferedImage binary = new BufferedImage(640, 480,
			BufferedImage.TYPE_BYTE_BINARY);

	private BufferedImage copy = new BufferedImage(640, 480,
			BufferedImage.TYPE_INT_RGB);


	Graphics2D g2d = binary.createGraphics();
	Graphics2D g2dImage = copy.createGraphics();
	Graphics2D g2dGrey = grey.createGraphics();
	
	private ScalesAndBarCode myScalesAndBarCode = null;
	private WeightAndCode myWeightAndCode = null;
	
	public BarCodePanels() {
		Dimension dim = Toolkit.getDefaultToolkit().getScreenSize();
		System.out.println("dim.height = " + dim.height + " dim.width = "
				+ dim.width);
		setBackground(Color.white);
		Dimension d = new Dimension(2 * HWIconst.camSizeX, 2 * HWIconst.camSizeY);
		setMinimumSize(d);
		setPreferredSize(d);
		decimalFormat = new DecimalFormat("#0.#"); // 1 decimal place
		msgFont = new Font("SansSerif", Font.BOLD, 15);
		myScalesAndBarCode = new ScalesAndBarCode();
		myScalesAndBarCode.start();
		new Thread(this).start(); // start updating the panel's image
	} // end of BarCodePanels()

	private BufferedImage makeGrey(BufferedImage inImage) {
		// Graphics2D g2dGrey = grey.createGraphics();
		g2dGrey.drawImage(inImage, 0, 0, null);
		// g2d.dispose();
		return grey;
	}

	private BufferedImage makeBinary(BufferedImage inImage) {
		// System.out.println("inImage.getWidth() = " + inImage.getWidth() + ", inImage.getHeight() = " + inImage.getHeight());
		// Graphics2D g2d = binary.createGraphics();
		g2d.drawImage(inImage, 0, 0, null);
		// g2d.dispose();
		return binary;
	}

	public void run()
	/* take a picture every DELAY ms */
	{

		System.out.println("At start of BarCodePanels.run()");
		camera = new CameraCapture();
		long duration;
		BufferedImage im = null;
		running = true;
		int modifyImage = 14;
		Image rawImage = null;
		while (running) {
			long startTime = System.currentTimeMillis();

			// im = camera.grabImage();  // take a snap

			rawImage = camera.grabRawCamImage(); // take a snap
			myWeightAndCode = myScalesAndBarCode.getWeightsAndCode();
			
			if (rawImage == null) {
				// if (im == null) {
				System.out.println("Problem loading image " + (imageCount + 1));
				duration = System.currentTimeMillis() - startTime;
				totalTime += duration;
			} else {
				modifyImage++;

				g2dImage.drawImage(rawImage, 0, 0, null);

				// image = im;   // only update image if im contains something
				image = copy; // only update image if im contains something
				imageCount++;
				// totalTime += duration;
				// System.out.println("Image " + imageCount + " loaded in " +
				//					 duration + " ms");

				if (modifyImage == HWIconst.elapsedGrabs) {

					greyImage = makeGrey(image);
					binaryImage = makeBinary(image);
					
					// Barcode decoding goes here!!!!!!!!!;

					modifyImage = 0;
					// repaint();
				}
				duration = System.currentTimeMillis() - startTime;
				totalTime += duration;

				repaint();
			}
			// duration = System.currentTimeMillis() - startTime;
			// totalTime += duration;
			if (duration < DELAY) {
				try {
					Thread.sleep(DELAY - duration); // wait until DELAY time has passed
				} catch (Exception ex) {
				}
			}
		}
		camera.close(); // close down the camera
	} // end of run()

	public void paintComponent(Graphics g)
	/* Draw the snap and add the average ms snap time at the 
	 bottom of the panel. */
	{
		super.paintComponent(g);
		g.drawImage(image, 0, 0, this); // draw the snap
		g.drawImage(greyImage, 640, 0, this); // draw the snap
		g.drawImage(binaryImage, 0, 480, this); // draw the snap
		g.setColor(Color.blue);
		g.setFont(msgFont);
		if (imageCount > 0) {
			double avgGrabTime = (double) totalTime / imageCount;
			g.drawString("Grab " + HWIHelper.padIntToString(imageCount, 5) + 
									", average time per grab =  " + 
									decimalFormat.format(avgGrabTime) +
									" ms", 690, 500);
			
			g.drawString("Weight 1 = " + 
					HWIHelper.padIntToString(myWeightAndCode.getWeight(1),4)
					, 690, 590);
			g.drawString("Weight 2 = " +  
					HWIHelper.padIntToString(myWeightAndCode.getWeight(2),4)
					, 690, 630);
			g.drawString("Code = " + 
					HWIHelper.padIntToString(myWeightAndCode.getCode(), 4)
					, 690, 670);
		
		} else {
			// no image yet
		}
	} // end of paintComponent()

	public void closeDown() {
	/* Terminate run() and wait for the camera to be closed.
	 This prevents exiting until everything
	 has finished. */
		myScalesAndBarCode.done();
		running = false;
		while (!camera.isClosed()) {
			try {
				Thread.sleep(DELAY);
			} catch (Exception ex) {
			}
		}
	} // end of closeDown()
}
