package selfCheckOut.hardWareInterface;


/**
 * This uninstantiable class is used to hold constants for the 
 * HardWareInterface system.
 * <p>
 * This class can not be instantiated.
 * 
 * @author Peter Gibney
 * @version 19th March 2008.
 */
public class HWIconst {
	//-------------------------------------------------------------
/**
 * This constructor is private.
 * <p>
 * Don't let anyone instantiate this class.
 */
private HWIconst() { }

//-------------------------------------------------------------
/** 
 * This is the frame rate for the camera.
 * 
 * @see CameraCapture
 */
public static final float FRAME_RATE = 24.0f; //15

//-------------------------------------------------------------
/** 
 * This is the horizontal dimension of a camera grabbed picture.
 * 
 * @see CameraCapture
 */

public static final int CAM_SIZE_X = 640;

//-------------------------------------------------------------

/** 
 * This is the vertical dimension of a camera grabbed picture.
 * 
 * @see CameraCapture
 */
public static final int CAM_SIZE_Y = 480;
//-------------------------------------------------------------
/** 
 * These are the offsets with respect to the first guard position 
 * for the other offsets in the printed representation of a barcode.
 * 
 */
static final int[] GUARD_REF_LOCATIONS = {0, 1, 2, 27, 28, 29, 30, 31, 56, 57, 58};//public 
//-------------------------------------------------------------
/** 
 * These are the the number of elements in GUARD_REF_LOCATIONS.
 * 
 */
public static final int NUM_GUARD_OFF_SETS = GUARD_REF_LOCATIONS.length;

//-------------------------------------------------------------
/** 
 * This is the number of spaces & black bars in a strip of code. 
 * 
 * @see BarCodePanels
 */

public static final int ITEMS_PER_STRIP = 59; //=(3 + 24 + 5 + 24 + 3);
//-------------------------------------------------------------
/** 
 * This is where the left group begins. 
 * 
 * @see BarCodePanels
 */

public static final int START_LEFT_GROUP = 3;//3 guard elements then data
//-------------------------------------------------------------
/** 
 * This is where the left group ends. 
 * 
 * @see BarCodePanels
 */

public static final int END_LEFT_GROUP = 26;//before middle guard elements
//-------------------------------------------------------------
/** 
 * This is where the right group begins. 
 * 
 * @see BarCodePanels
 */

public static final int START_RIGHT_GROUP = 32;//after middle guard elements
//-------------------------------------------------------------
/** 
 * This is where the right group ends. 
 * 
 * @see BarCodePanels
 */
public static final int END_RIGHT_GROUP = 55;//before right guard elements
//-------------------------------------------------------------
/** 
 * This is the number of bar/space units in a strip of code. 
 * 
 * 3 of unit length in left guard, 6 numbers in left at 7 units,
 * 5 of unit length in centre guard, 6 numbers in right at 7 units,
 * 3 of unit length in right guard = 95
 * @see BarCodePanels
 */

public static final int NUM_BAR_SPACE_UNITS = 3 + 6*7 + 5 + 6*7 + 3;//=95 
//-------------------------------------------------------------
/** 
 * This is the max permitted width of bar/space in pixels. 
 * 
 * calculated from width of screen divided by number of unit
 * lengths in a strip; plus a bit to account for focus errrors,
 * and not having the camera and barcode paralell.
 * 
 * @see BarCodePanels
 */

public static final int MAX_UNIT_WIDTH =(CAM_SIZE_X/NUM_BAR_SPACE_UNITS)+ 5;
// needs to be changed if using camera > 640 * 480
//-------------------------------------------------------------
/** 
 * This is the min permitted width of bar/space in pixels. 
 * 
 * @see BarCodePanels
 */

public static final int MIN_UNIT_WIDTH = 1; 
// needs to be changed if using camera > 640 * 480
//-------------------------------------------------------------
/** 
 * This is the max permitted width diff of guard bar/space in pixels. 
 * 
 * @see BarCodePanels
 */

public static final int MAX_GUARD_ELEMENT_WIDTH = 8; //was 6 
// needs to be changed if using camera > 640 * 480
// make it adaptave 
//-------------------------------------------------------------

/** 
 * This is how much the mean length of a line of bars 
 * can differ from theory.
 * 
 */
public static final double SCAN_LEN_TOLERANCE = 1.16; //1.06
//-------------------------------------------------------------
/** 
 * This is the value of a white pixel in a binary image.
 * 
 */
public static final int BINARY_WHITE = 255; //used in threshold detection
//-------------------------------------------------------------	
/** 
 * This is how much the variation in the length 
 * of a guard bar is allowed.
 */
public static final double SCAN_BAR_VAR = 0.4;

//-------------------------------------------------------------
/** 
 * This is whether we want general debug output.
 */
public static final boolean DE_BUG = false;
//-------------------------------------------------------------
/** 
 * This is whether we want debug output for filtering.
 */
public static final boolean DE_BUG_FILTERING = false;
//-------------------------------------------------------------
/** 
 * This is whether we want shut down debugging output, 
 * use this to see if there are any threads not shutting down.
 */
public static final boolean DE_BUG_THREAD_SHUT_DOWN = false;	
//-------------------------------------------------------------
/** 
 * This is the number of elapsed camera grabs between each 
 * attempt to read a bar code.
 * 
 * @see BarCodePanels
 */
public static final int ELAPSED_GRABS = 20;
//-------------------------------------------------------------
/** 
 * This is used in debugging and development it shows if the 
 * producer/consumer are interleaved correctly.
 * 
 * @see BarCodePanels
 */
public static final boolean SHOW_INTER_LEAVING = false;
//-------------------------------------------------------------
static final String[] binaryType = //public
	{"RGB", "RG", "RB", "GB", "R", "G", "B", "ALL"}; 



}//end class
