package selfCheckOut.hardWareInterface;


/**
 * This  class is used generate binary and grey images to be scanned for 
 * a barcode, it creates them from red green & blue; red & green; red & blue;
 * green & blue; red; green; blue, this way the chances of getting a readable
 * barcode are improved, the binarization process makes use of a sliding
 * window across the image and the threshold is based on the average 
 * value in that window.
 * <p>
 * 
 * @author Peter Gibney
 * @version 31st March 2008.
 */



import java.awt.image.*;
import java.awt.*;
public class ImageMaker {

	private BufferedImage sourceImage = null;
	private BufferedImage[] greyImages = null; 
	private BufferedImage[] binImages = null; 
	
	private static final int[][] IMAGE_CODES = 
		{{1, 1, 1},	//RGB
		{1, 1, 0},	//RG
		{1, 0, 1},	//RB
		{0, 1, 1},	//GB
		{1, 0, 0},	//R
		{0, 1, 0},	//G
		{0, 0, 1}};	//B
	int Xsize = 0;
	int Ysize = 0;
	
	/**
	 * 
	 */
	public ImageMaker(BufferedImage inImage) {
		//this.sourceImage = inImage;
		if (inImage != null)
			makeImages(inImage);
	}
	//------------------------------------------------------------------
	public BufferedImage getSourceImage() {
		return sourceImage;
	}
	//------------------------------------------------------------------
	public void makeImages(BufferedImage inImage) {
		this.sourceImage = inImage;
		Xsize = sourceImage.getWidth();
		Ysize = sourceImage.getHeight();
			greyImages = new BufferedImage[7];
			for (int i = 0; i < 7; i++) {
				greyImages[i] = new BufferedImage(Xsize, 
									Ysize, 
									BufferedImage.TYPE_INT_RGB);
			}
		if (binImages == null) 
			binImages = new BufferedImage[7]; 
		
		for (int x=0;x<Xsize;x++){
			for (int y=0;y<Ysize;y++){
				Color pixelColour = new Color(sourceImage.getRGB(x, y), false);
				int redCol = pixelColour.getRed();
				int greenCol = pixelColour.getGreen();
				int blueCol = pixelColour.getBlue();
				for (int i = 0; i < 7; i++) {
					int greyCol = 0;
					greyCol = greyCol + (redCol * IMAGE_CODES[i][0]);
					greyCol = greyCol + (greenCol * IMAGE_CODES[i][1]);
					greyCol = greyCol + (blueCol * IMAGE_CODES[i][2]);
					greyCol = greyCol/
								(IMAGE_CODES[i][0] + 
									IMAGE_CODES[i][1] +
									IMAGE_CODES[i][2]);
					
					pixelColour= new Color(greyCol, greyCol, greyCol);
					greyImages[i].setRGB(x, y, pixelColour.getRGB());
				}
			}
		}
		try {
			Thread.sleep(28);
		} catch (InterruptedException e) {
			e.printStackTrace();
			System.out.println("Interrupted in Image Maker...");
		}
		int[][] intSource = new int[Ysize][Xsize];
		for (int i = 0; i < 7; i++) {
			for (int x=0;x<Xsize;x++){
				for (int y=0;y<Ysize;y++){
					Color pixelColour = new Color(greyImages[i].getRGB(x, y), false);
					int redCol = pixelColour.getRed();
					int greenCol = pixelColour.getGreen();
					int blueCol = pixelColour.getBlue();
					intSource[y][x] = (redCol + greenCol + blueCol)/3;  
				}
			}
			binImages[i] = integralImage(intSource);
			try {
				Thread.sleep(28);
			} catch (InterruptedException e) {
				e.printStackTrace();
				System.out.println("Interrupted in Image Maker...");
			}
		}
	}
	//------------------------------------------------------------------
	public BufferedImage getGreyImage(int imageType) {
		if (imageType == 7)
			imageType = 0;
		return greyImages[imageType];
	}
	// ------------------------------------------------------	
	public BufferedImage getBinaryImage(int imageType) {
		if (imageType == 7)
			imageType = 0;
		return binImages[imageType];
	}
	//------------------------------------------------------
	private BufferedImage integralImage(int[][] inPutMatrix) {
		int ySize = inPutMatrix.length;
		int xSize = inPutMatrix[0].length;
		int[][] outPutMatrix = new int[ySize][xSize];
		for (int xPos = 0; xPos < xSize; xPos++) {
			int sum = 0;
			for (int yPos = 0; yPos < ySize; yPos++) {
				sum += inPutMatrix[yPos][xPos];
				if (xPos==0)
					outPutMatrix[yPos][xPos] = sum;
				else
					outPutMatrix[yPos][xPos] = outPutMatrix[yPos][xPos-1] + sum;
			}
		}
		BufferedImage greyImage = new BufferedImage(xSize, 
									ySize, 
									BufferedImage.TYPE_INT_RGB);
		int s = xSize/8;
		double threshold = 0.15d;
		// perform thresholding
		for (int xPos = 0; xPos < xSize; xPos++) {
			for (int yPos = 0; yPos < ySize; yPos++) {
				// set the SxS region
				int x1=xPos-s; 
				int x2=xPos+s;
				int y1=yPos-s; 
				int y2=yPos+s;
				// check the border
				if (x1 < 0) 
					x1 = 0;
				if (x2 >= xSize) 
					x2 = xSize-1;
				if (y1 < 0) 
					y1 = 0;
				if (y2 >= ySize) 
					y2 = ySize-1;
				
				int count = (x2-x1)*(y2-y1);
				
				int sum = outPutMatrix[y2][x2] -
							outPutMatrix[y2][x1] -
							outPutMatrix[y1][x2] +
							outPutMatrix[y1][x1];

				Color pixelColour= Color.black;
				double adjThresh = 1.0d -threshold;
				if ((inPutMatrix[yPos][xPos] * count) <= (((double)sum *adjThresh))) {
					pixelColour= Color.black;
				} else {
					pixelColour= Color.white;
				}
				greyImage.setRGB(xPos, yPos, pixelColour.getRGB());
			}
		}
		BufferedImage binImage = new BufferedImage(xSize, ySize, BufferedImage.TYPE_BYTE_BINARY); 
		Graphics2D graphicBinary = binImage.createGraphics();
		graphicBinary.drawImage(greyImage, 0, 0, null);
		graphicBinary.dispose();
		return binImage;
	}
}
