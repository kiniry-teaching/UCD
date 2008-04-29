package selfCheckOut;
	/**
	 * This class is used in grabbing and displaying the Barcodes and weights
	 * and for onward transmission through the network to the primary 
	 * SelfCheckOut program.
	 * To run and compile it is necessary to have the Java Media Framework,
	 * JMF
	 * <p>
	 * 
	 * @author Peter Gibney
	 * @version 23rd March 2008.
	 */

import java.awt.*;
import java.util.Random;
import javax.swing.*;
import java.awt.image.*;
import java.util.Date;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import selfCheckOut.hardWareInterface.*;
import javax.media.*;
import javax.media.format.VideoFormat;
import javax.media.util.BufferToImage;
import selfCheckOut.netWork.PumpReciever;
import selfCheckOut.netWork.ResultPumper;

class BarCodePanels extends JPanel implements Runnable {
	
	private static final long serialVersionUID = 2870378;
	
	private static final int DELAY = 50; 	// Grab a picture every Delay ms
	private CameraCapture camera = null;
	private Decoder decoder = null;
	private boolean stopRequested = false; //we have not been requestede to stop

	// used for the average ms snap time info
	private int imageCount = 0;
	private long totalTime = 0;
	private Font msgFont;

	private BufferedImage imageGrey = new BufferedImage(640, 480,
			BufferedImage.TYPE_BYTE_GRAY);

	BufferedImage imageBinary = new BufferedImage(640, 480,
			BufferedImage.TYPE_BYTE_BINARY);

	private BufferedImage imageColour = new BufferedImage(640, 480,
			BufferedImage.TYPE_INT_RGB);

	Graphics2D graphicColour = imageColour.createGraphics();
	
	BarCode code = null; //the decoded barcode
	private PumpReciever pumpReceiver = null;
	private HardWareResult myHWR = null;
	private ResultPumper resultPumper = null;
	
	private volatile boolean latestScreenDrawn = false; //true; // assume screen is drawn and we are ready to compute new data
	private boolean drawGreyPic = true;
	private boolean drawBinaryPic = true;
	
	private Random laserLine = new Random();
	
	private int imageType = -1;
	private int[] compGrab1 = new int[640];
	private BufferToImage bufferToImage = null;
	String persistCode = "?????";
	String persistW1 = "?????";
	String persistW2 = "?????";
	
	// ------------------------------------------------------
	public BarCodePanels(String AddressIP) {
		camera = new CameraCapture();
		Dimension dim = Toolkit.getDefaultToolkit().getScreenSize();
		System.out.println("dim.height = " + dim.height + " dim.width = "
				+ dim.width);
		setBackground(Color.white);
		Dimension d = new Dimension(2 * HWIconst.CAM_SIZE_X, 2 * HWIconst.CAM_SIZE_Y);
		setMinimumSize(d);
		setPreferredSize(d);
		msgFont = new Font("SansSerif", Font.BOLD, 15);
		pumpReceiver = new PumpReciever(AddressIP, 4444);
		pumpReceiver.start();
		pumpReceiver.gather(true);
		resultPumper = new ResultPumper(3333);
		resultPumper.start();
		decoder = new Decoder();
		//decoder.start();
		new Thread(this).start(); // start updating the panel's image
	} // end of BarCodePanels()
//---------------------------------------------------
	private String getDateTime() {
		DateFormat dateFormat = new SimpleDateFormat("HH:mm:ss dd/MM/yyyy");
		Date date = new Date();
		return dateFormat.format(date);
	}
	//-----------------------------------------------------------------------
	/** method to try to detect if the image has changed since last grab
	 * return null if unchanged from last time
	 * 
	 */
	private Buffer hasFrameChanged(Buffer inBuff) {
		assert inBuff != null;
		Object outdata = inBuff.getData();
		byte[] buffArray =  (byte[])outdata;
		boolean changed = false;
		if (outdata instanceof byte[]) { // 
			for (int x=0;x< 640; x++) {
				int pos = (((x)/2)*9*320) + (7*18*(x/(6*7)));
				pos = pos + x%3;
				int grabInt = ((256 + (int) buffArray[pos]) % 256);
				if (grabInt != compGrab1[x]) {
					changed = true;
					compGrab1[x] = grabInt;
				}
				/*
				buffArray[pos] = -1; //mark out the pixel either R,G, or B
				*/
			}
			if (!changed) {
				//System.out.print(" SAME 2 ");
			}
		} else {
			System.out.println("expecting a byte array..");
		}
		if (!changed)
			return null;
		return inBuff;
	}
	//---------------------------------------------------
	private Image grabRawImage() {
		Image rawImage = null;
		Buffer grabbedFrame = camera.grabFrame();
		if (grabbedFrame != null) {
			grabbedFrame = hasFrameChanged(grabbedFrame);
			if (grabbedFrame != null) {
				// there is a buffer, but check if it's empty or not
				if (bufferToImage == null) {
					//have not initialized it before
					System.out.println("//have not initialized it before");
					VideoFormat vf = (VideoFormat) grabbedFrame.getFormat();
					if (vf == null) {
						System.out.println("No video format in  direct grabbed buffer");
					} else {
						System.out.println("Direct Grabbed Video format: " + vf);
						bufferToImage = new BufferToImage(vf);
						rawImage = bufferToImage.createImage(grabbedFrame);
					}
				} else {
					rawImage = bufferToImage.createImage(grabbedFrame);
				}
			}
		}
		return rawImage;
	}
	//---------------------------------------------------
	public void run(){
	/* grab a picture every DELAY ms */
		System.out.println("At start of BarCodePanels.run()");
		long duration = 0;
		int modifyImage = 15;
		Image rawImage = null;
		synchronized(this) {
			myHWR = pumpReceiver.getHardWareResult();
		}
		boolean waitingForCam = true;
		while (waitingForCam) {
			rawImage = grabRawImage();
			waitingForCam = (rawImage == null);
			if (waitingForCam) {
				try {
					Thread.sleep(50);
				} catch (Exception ex) {
					ex.printStackTrace();
				}
			}
		}
		decoder.start();
		graphicColour.drawImage(rawImage, 0, 0, null);
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
				long startTime = System.currentTimeMillis();
				rawImage = grabRawImage();
				if (rawImage == null) {
					//System.out.println("Problem loading image " + (imageCount + 1));
					duration = System.currentTimeMillis() - startTime;
					duration = Math.max(duration,27);
					totalTime += duration;
				} else {
					graphicColour.drawImage(rawImage, 0, 0, null);
					graphicColour.setColor(Color.RED);
					graphicColour.setFont(new Font("Helvetica",Font.BOLD,12));
					graphicColour.drawString(HWIHelper.padIntToString(modifyImage, 6), 5, 14);
					imageCount++;
					if (decoder.determineCode(imageColour, 
							System.currentTimeMillis())) {
						imageBinary = null; //erase older one
						imageGrey = null;
						code = null;
						drawBinaryPic = true;
						drawGreyPic = true; //going to need to refresh the grey picture
						if (HWIconst.DE_BUG) {
							System.out.println("??????? ACCEPTED ?????????????????");
						}
					}
					//modifyImage = 1;
					
					HardWareResult tempHWR = pumpReceiver.getHardWareResult();
					if (tempHWR != null) {
						myHWR = tempHWR;
					}
					//myHWR = tempHWR;
					//myHWR = pumpReceiver.getHardWareResult();
					//System.out.println("myHWR = " + myHWR);
					if (modifyImage >= HWIconst.ELAPSED_GRABS) {
						imageType++;
						if (imageType == 7) 
						imageType = 0;
						modifyImage = 0;
					}
					DecoderResult decRes = decoder.getResult();
					if (decRes != null) {
						System.out.println("<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<");
						code = decRes.getBarCode();
						System.out.println(code);
						System.out.println(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");
						imageBinary = decRes.getBinaryImage();
						imageGrey = decRes.getGreyImage();
						BarCode[] theBarCode = null;//new BarCode[1];
						//System.out.println("myHWR = " + myHWR);
						if (code != null) {
							theBarCode = new BarCode[1];
							theBarCode[0] = code;
							if (myHWR != null) {
								myHWR = new HardWareResult(theBarCode,
														myHWR.getWeight(0),
														myHWR.getWeight(1));
							} else {
								myHWR = new HardWareResult(theBarCode,
										null,
										null);
							}
						} else {
							if (myHWR != null) {
								if ((myHWR.getWeight(0) != null) && (myHWR.getWeight(1) != null))  {
									myHWR = new HardWareResult(null,
														myHWR.getWeight(0),
														myHWR.getWeight(1));
								}
							}
						}
						drawBinaryPic = true;
						drawGreyPic = true; //going to need to refresh the grey picture
					} else {
						//imageBinary = null;
					}
					if (myHWR != null) {
						System.out.println("myHWR = " + myHWR);
						resultPumper.pumpResults(myHWR);
					}
					duration = System.currentTimeMillis() - startTime;
					totalTime += duration;
					//System.out.print(" D ");
					latestScreenDrawn = false; //going to need an update to the screen
					notifyAll();
					repaint();
				}				
					modifyImage++;
			} // release  sync
			
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
		synchronized(this) {
			assert Thread.holdsLock(this);
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
			g.drawImage(imageColour, 0, 0, this); // draw the snap
			g.setColor(Color.red);
			int laserPos = 220 + laserLine.nextInt(29);
			g.drawLine(0, laserPos, 640, laserPos);
			
			if (drawGreyPic) {
				if (imageGrey == null) {
					g.clearRect(640, 0, 1280, 480);
				}else {
					g.drawImage(imageGrey, 640, 0, this); // draw the snap
				}
			}
			if (drawBinaryPic) {
				if (imageBinary == null) {
					g.clearRect(0, 480, 640, 960);
				} else {
					g.drawImage(imageBinary, 0, 480, this); // draw the snap
				}	
			}
			g.clearRect(640, 480, 640, 480);
			g.setColor(Color.blue);
			g.setFont(msgFont);
			if (imageCount > 0) {
				if (myHWR !=null) {
					if (myHWR.getWeight(0) != null) {
						persistW1 = HWIHelper.padIntToString(myHWR.getWeight(0).getWeightInt(),4);
					}
					if (myHWR.getWeight(1) != null) {
						persistW2 = HWIHelper.padIntToString(myHWR.getWeight(1).getWeightInt(),4);
					}
					if (myHWR.getBarCodes() != null) {
						if (myHWR.getBarCodes()[0] != null) {
							persistCode = myHWR.getBarCodes()[0].toString();
							g.drawString("Prob= " + myHWR.getBarCodes()[0].getProbability() , 890, 550);
						}
					}
				}
				g.drawString("Code = " + persistCode , 690, 550);
				g.drawString("Weight 1 = " + persistW1, 690, 590);
				g.drawString("Weight 2 = " +  persistW2, 690, 630);
				g.drawString(getDateTime(), 690, 750); 
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
			pumpReceiver.done();
			resultPumper.done();
			decoder.done();
		} //end sync
		
		while (!camera.isClosed() || !pumpReceiver.isStopped()|| !decoder.isStopped()) {
			if (HWIconst.DE_BUG_THREAD_SHUT_DOWN) {
				System.out.println("in BarCodePanels.closeDown(), waiting:");
				System.out.println("        camera.isClosed() : " + 
						camera.isClosed());
				System.out.println("        myScalesClient.isClosed() : " + 
						pumpReceiver.isStopped());
				
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
	
} //end class
