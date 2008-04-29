package selfCheckOut.hardWareInterface;
import java.awt.image.BufferedImage;
import selfCheckOut.*;

/**
 * This class is used to return the result from Decoder,
 * it contains barcode, binary image and greyimage for display on the
 * development consol.
 * <p>
 * 
 * @author Peter Gibney
 */

public class DecoderResult {

	BufferedImage greyImage = null;	
	BufferedImage binImage = null;
	BarCode barNums = null;
	
	public DecoderResult(BufferedImage greyImage,	
							BufferedImage binImage,
							BarCode barNums) {
		this.greyImage = greyImage;	
		this.binImage = binImage;
		this.barNums = barNums;
	}
	//------------------------------------------------------
	public BufferedImage getGreyImage() {
		return this.greyImage;
	}
	//------------------------------------------------------
	public BufferedImage getBinaryImage() {
		return this.binImage;
	}
	//------------------------------------------------------
	public BarCode getBarCode() {
		return this.barNums;
	}
}//end class
