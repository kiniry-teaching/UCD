	/**
	 * This uninstantiable class is used to hold constants for the 
	 * HardWareInterface system.
	 * <p>
	 * This class can not be instantiated.
	 * 
	 * @author Peter Gibney
	 * @version 10th March 2008.
	 */
public class HWIconst {

	
	/**
	 * This constructor is private.
	 * <p>
	 * Don't let anyone instantiate this class.
	 */
	private HWIconst() { }
	
//-------------------------------------------------------------
	/** 
	 * These are the offsets with respect to the first guard position 
	 * for the other offsets in the printed representation of a barcode.
	 * 
	 */
	public static final int[] guardRefLocations = {0, 1, 2, 27, 28, 29, 30, 31, 56, 57, 58};
	//-------------------------------------------------------------
	/** 
	 * These are the the number of elements in guardRefLocations.
	 * 
	 */
	public static final int numGuardOffSets = guardRefLocations.length;
	
	//-------------------------------------------------------------
	
	/** 
	 * This is how much the mean length of a line of bars 
	 * can differ from theory.
	 * 
	 */
	public static final double scanLenTolerance = 1.06;


	//-------------------------------------------------------------
	
	/** 
	 * This is how much the variation in the length 
	 * of a guard bar is allowed.
	 */
	public static final double scanBarVar = 1.5;
	
	//-------------------------------------------------------------
	/** 
	 * This is whether we want debug output.
	 */
	public static final boolean deBug = false;

	//-------------------------------------------------------------
	/** 
	 * This is the frame rate for the camera.
	 * 
	 * @see CameraCapture
	 */
	public static final float frameRate = 15.0f;
	
	//-------------------------------------------------------------
	/** 
	 * This is the horizontal dimension of a camera grabbed picture.
	 * 
	 * @see CameraCapture
	 */
	
	public static final int camSizeX = 640;

	//-------------------------------------------------------------

	/** 
	 * This is the vertical dimension of a camera grabbed picture.
	 * 
	 * @see CameraCapture
	 */
	public static final int camSizeY = 480;
	//-------------------------------------------------------------
	/** 
	 * This is the number of elapsed camera grabs between each 
	 * attempt to read a bar code.
	 * 
	 * @see BarCodePanels
	 */
	public static final int elapsedGrabs = 15;
	
}//end class
