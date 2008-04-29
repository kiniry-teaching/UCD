package selfCheckOut.hardWareInterface;
import java.awt.*;
import java.util.*;
import javax.media.*;
import javax.media.control.*;
import javax.media.format.*;
import javax.media.control.FrameGrabbingControl;
import selfCheckOut.hardWareInterface.*;

//http://www.reza-nazarian.de/computer/Java/jmf.htm
//http://www.sun.com/software/communitysource/jmf/download.xml
//http://forum.java.sun.com/thread.jspa?forumID=28&threadID=570463
//http://java.sun.com/products/java-media/jmf/2.1.1/solutions/screengrabber/LiveStream.java
//http://fivedots.coe.psu.ac.th/~ad/jg2/ch09/index.html

//http://java.sun.com/products/java-media/jmf/2.1.1/apidocs/javax/media/control/FrameGrabbingControl.html#grabFrame()
//http://java.sun.com/products/java-media/jmf/2.1.1/apidocs/javax/media/Buffer.html
//http://www.onjava.com/pub/a/onjava/2005/06/01/kgpjava.html?page=last
//http://java.sun.com/products/java-media/jmf/2.1.1/solutions/FrameAccess.java
//http://www.comp.rgu.ac.uk/staff/fh/CM4062/mis/jmf/FrameGrab.html
//http://algoval.essex.ac.uk/software/video/JavaRTVK.html
//http://java.sun.com/products/java-media/jmf/2.1.1/solutions/screengrabber/LiveStream.java
//http://www.erde.co.jp/~katsu/wiki/index.php?JMF(Java%20Media%20Framework)%A4%C7%CD%B7%A4%F3%A4%C7%A4%DF%A4%BF
//System.out.println(buf.getLength());



/**
 * This class is used to grab images from the camera for the HardWareInterface system, 
 * the JMF must be installed to operate.
 * <p>
 * This classs is adopted from code and information on the following sites:
 * <p>
 * http://www.reza-nazarian.de/computer/Java/jmf.htm
 * <p>
 * http://www.sun.com/software/communitysource/jmf/download.xml
 * <p>
 * http://forum.java.sun.com/thread.jspa?forumID=28&threadID=570463
 * <p>
 * http://java.sun.com/products/java-media/jmf/2.1.1/solutions/screengrabber/LiveStream.java
 * <p>
 * http://fivedots.coe.psu.ac.th/~ad/jg2/ch09/index.html
 * <p>
 *
 * @author Peter Gibney using code and examples from the above links.
 * 
 * @version 23rd March 2008.
 * 
 * @see HWIconst
 */

public class CameraCapture implements ControllerListener {

	// used while waiting for the BufferToImage object to be initialized
	private static final int MAX_TRIES = 25;
	private static final int TRY_PERIOD = 1000; // ms

	private Player camPlayer;
	private FrameGrabbingControl frameGrabControl;
	volatile private boolean closedDevice;

	// used for waiting until the player has started
	private Object waitSync = new Object();
	private boolean stateTransitionOK = true;

	private CaptureDeviceInfo devInfo = null;

	private int dataSize = HWIconst.CAM_SIZE_X * HWIconst.CAM_SIZE_Y * 3;
	
	private Dimension camDim = new Dimension(HWIconst.CAM_SIZE_X, HWIconst.CAM_SIZE_Y);
	
	private VideoFormat desiredFormat = 
			new VideoFormat("RGB", camDim, dataSize/*921600*/, byte[].class, HWIconst.FRAME_RATE);
	//http://java.sun.com/products/java-media/jmf/2.1.1/solutions/
	// http://java.sun.com/products/java-media/jmf/2.1.1/solutions/screengrabber/LiveStream.java
	//http://java.sun.com/products/java-media/jmf/2.1.1/apidocs/javax/media/format/VideoFormat.html

	/**
	 * Constructs the object to grab a frame from the camera. 
	 */
	// ------------------------------------------------------
	public CameraCapture() {
		closedDevice = true; // since device is not available yet
		MediaLocator mediaLoc = null;
		// link player to capture device
		try {
			//mediaLoc = findMedia(CAP_DEVICE);
			mediaLoc = findMedia("vfw:Microsoft WDM Image Capture (Win32):0");
			System.out.println("About to Create player");
			camPlayer = Manager.createRealizedPlayer(mediaLoc);
			System.out.println("Created player");
		}
		catch (Exception e) {
			System.out.println("Failed to create camera player");
			System.out.println("CameraCapture() exception = " + e.toString());
			e.printStackTrace();
			throw new RuntimeException("Failed to create camera player",e);
		}
		FormatControl formatControl = null;
		formatControl = (FormatControl) 
						camPlayer.getControl("javax.media.control.FormatControl");
		Format currFormat = formatControl.getFormat();
		Format[] videoFormats = null;
		videoFormats = devInfo.getFormats();
		System.out.println(">>> capture video device = " + devInfo.getName());
		System.out.println("Numbe of video formats is " + videoFormats.length);

		// display device formats
		for (int y = 0; y < videoFormats.length; y++) {
			Format aFormat = videoFormats[y];
			if (aFormat instanceof VideoFormat) {
				Dimension dim = ((VideoFormat) aFormat).getSize();
				System.out.println("Video Format " + y + " : "
						+ videoFormats[y].getEncoding() + ", " + dim.width
						+ " x " + dim.height);
			}
		}
		if (currFormat instanceof VideoFormat) {
			Dimension dim = ((VideoFormat) currFormat).getSize();
			System.out.println("Curr Video Format: " + currFormat.getEncoding()
					+ ", " + dim.width + " x " + dim.height);

		} else {
			System.out.println("Error : Cannot get current video format");
		}

		formatControl.setFormat(desiredFormat);

		// formatControl.setFormat (videoFormats[4]);
		currFormat = formatControl.getFormat();

		if (currFormat instanceof VideoFormat) {
			Dimension dim = ((VideoFormat) currFormat).getSize();
			System.out.println("Curr Video Format: " + currFormat.getEncoding()
					+ ", " + dim.width + " x " + dim.height);

		} else {
			System.out.println("Error : Cannot get current video format");
		}

		camPlayer.addControllerListener(this);

		// create the frame grabber
		frameGrabControl = 
			(FrameGrabbingControl) 
			camPlayer.getControl("javax.media.control.FrameGrabbingControl");
		if (frameGrabControl == null) {
			System.out.println("Frame grabber could not be created");
			System.exit(0);
		}

		// wait until the player has started
		System.out.println("Starting the player...");
		camPlayer.start();
		if (!waitForStart()) {
			System.err.println("Failed to start the player.");
			System.exit(0);
		}
		waitForImage();
	} // end of CameraCapture()
	// ------------------------------------------------------
	/**
	 * Searches for the specified camera. 
	 * 
	 * @param  requireDeviceName the name of the device to capture, 
	 * the name is obtainable using the JMF registry tool.
	 * 
	 * @return a MediaLocator for the specified capture device.
	 */
	private MediaLocator findMedia(String requireDeviceName) {
		assert requireDeviceName != null;
		// return a media locator for the specified capture device
		//line Vector devices = CaptureDeviceManager.getDeviceList(null);

		
		Vector devices = CaptureDeviceManager.getDeviceList(new VideoFormat(VideoFormat.RGB));
		if (devices == null) {
			System.out.println("Devices list is null");
			//System.exit(0);
		} else {
			if (devices.size() == 0) {
				System.out.println("No devices found.....");
				//System.exit(0);
			}
		}
		System.out.println(devices.size() + " devices found");

		// VideoFormat format = new VideoFormat("RGB", new Dimension(176, 144), 76230, byte[].class, 15.0f);
		// DataSource ds;
		for (int i = 0; i < devices.size(); i++) {
			// CaptureDeviceInfo devInfo = (CaptureDeviceInfo) devices.elementAt(i);
			devInfo = (CaptureDeviceInfo) devices.elementAt(i);
			String devName = devInfo.getName();
			if (devName.equals(requireDeviceName)) { // found device
				devInfo = (CaptureDeviceInfo) devices.elementAt(i);

				System.out.println("Found device: " + requireDeviceName);
				System.out.println("About to return");
				return devInfo.getLocator(); // this method may not work
			}
		}
		System.out.println("Device " + requireDeviceName + " not found");
		System.out.println("Using default media locator: ");
		return new MediaLocator("vfw:// 0");
	} // end of findMedia()

	/**
	 * Wait for the player to enter its Started state.
	 
	 * @return true when the camera services are available.
	 * 
	 */
	private boolean waitForStart() {
	// wait for the player to enter its Started state
		synchronized (waitSync) {
			try {
				while (camPlayer.getState() != Controller.Started && stateTransitionOK)
					waitSync.wait();
			} catch (Exception e) {
				System.out.println("CameraCapture() exception = " + e.toString());
				e.printStackTrace();
			}
		}
		return stateTransitionOK;
	} // end of waitForStart()

	/**
	 * Wait for the Image object to be initialized.
	 * May take several seconds to initialize this object, 
	 * so this method makes up to MAX_TRIES attempts.
	 * 
	 */
	private void waitForImage(){
		int tryCount = MAX_TRIES;
		System.out.println("Initializing Image...");
		while (tryCount > 0) {
			if (hasImage()) // initialization succeeded
				break;
			try { // initialization failed so wait a while and try again
				System.out.println("Waiting...");
				Thread.sleep(TRY_PERIOD);
			} catch (InterruptedException e) {
				System.out.println("CameraCapture " + e.toString());
				e.printStackTrace();
			}
			tryCount--;
		}
		if (tryCount == 0) {
			System.out.println("Giving Up");
			System.exit(0);
		}
		closedDevice = false; // device now available
	} // end of waitForImage()

	
	/**
	 * The object is initialised by taking a snap, which
	 * may be an actual picture or be 'empty'.
	 *<p>
	 * An 'empty' snap is a Buffer object with no video information,
	 * as detected by examining its component VideoFormat data. 
	 *<p>
	 * @return true if the buffer to the image is available
	 * 
	 */
	synchronized private boolean hasImage() {
		Buffer buf = frameGrabControl.grabFrame(); // take a snap
		if (buf == null) {
			System.out.println("No grabbed frame");
			return false;
		}
		// there is a buffer, but check if it's empty or not
		VideoFormat vf = (VideoFormat) buf.getFormat();
		if (vf == null) {
			System.out.println("No video format");
			return false;
		}
		System.out.println("Video format: " + vf);
		//System.exit(0);
		return true;
	} // end of hasImage()
	//-----------------------------------------------------------------------
	/**
	 * Grab the frame buffer from the camera.
	 * 
	 * @return Buffer the current frame.
	 */
	synchronized public Buffer grabFrame() {
		if (closedDevice)
			return null;
		Buffer buf = frameGrabControl.grabFrame();
		if (buf == null) {
			System.out.println("[No grabbed buffer]");
			return null;
		}
		return buf;
	}
	//-----------------------------------------------------------------------
	/**
	 * Shuts down the camera interface.
	 * <p>
	 * close() and grabRawCamImage() are synchronized so that it's not
	 * possible to close down the player while a frame is being snapped.
	 */
	synchronized public void close(){
	/* close() and grabImage() are synchronized so that it's not
	 possible to close down the player while a frame is being
	 snapped. */
		camPlayer.close();
		closedDevice = true;
	}
	/**
	 * Queries the state of the camera interface.
	 * 
	 * @return whether the camera interface is closed or not, true for closed.
	 */
	synchronized public boolean isClosed() {
		return closedDevice;
	}
	/**
	 * The type CameraCapture must implement the inherited abstract method:
	 * ControllerListener.controllerUpdate(ControllerEvent).
	 * 
	 * @param  event the event to listen to.
	 * 
	 */
	public void controllerUpdate(ControllerEvent event) {
	// respond to events
		if (event instanceof StartEvent) { // the player has started
			synchronized (waitSync) {
				stateTransitionOK = true;
				waitSync.notifyAll();
			}
		} else if (event instanceof ResourceUnavailableEvent) {
			synchronized (waitSync) { // there was a problem getting a player resource
				stateTransitionOK = false;
				waitSync.notifyAll();
			}
		}
	} // end of controllerUpdate()

} // end of CameraCapture class
