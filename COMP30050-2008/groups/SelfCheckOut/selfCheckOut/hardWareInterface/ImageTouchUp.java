package selfCheckOut.hardWareInterface;
import java.awt.Color;
import java.awt.Font;
import java.awt.Graphics2D;
import java.awt.image.BufferedImage;


/**
 * This class is used to draw on top of the image where the barcode was 
 * found, it was used in the development of the algorithm.
 * <p>
 * 
 * @author Peter Gibney
 * @version 31st March 2008.
 */


public class ImageTouchUp {
	private int[][] touchUpInfo = null;
	private boolean hasRegressionLine = false;
	private double intercept = 0d;
	private double slope = 0d;

		public ImageTouchUp() {
			touchUpInfo = new int[480][3];
			for (int i = 0; i < 480; i++) {
				//reset line info for screen writing
				touchUpInfo[i][0] = -1; //-1 = no info on this line
				touchUpInfo[i][1] = 0; // starting positon
				touchUpInfo[i][2] = 0; // stopping positon
			}
		}
		
		public void storeTouch(BarCodeStripe inPutStripe, int colour) {
			int lineNo = inPutStripe.getLineNum();
			touchUpInfo[lineNo][0] = colour;
			touchUpInfo[lineNo][1] = inPutStripe.getStart();
			touchUpInfo[lineNo][2] = inPutStripe.getEnd();
		}
		//---------------------------------------------
		public BufferedImage touchUpImage(BufferedImage inImage) {
			Graphics2D graph = inImage.createGraphics();
			graph.setColor(Color.blue);
			graph.drawImage(inImage, 0, 0, null);
			graph.setFont(new Font("Helvetica",Font.BOLD,24));
			for (int i = 0; i < 480; i++) {
				int colour = touchUpInfo[i][0];
				if (colour >= 0) {
					switch (colour) {
						case 0:	{
							graph.setColor(Color.blue);
							break;
						}

						case 1:	{
							graph.setColor(Color.green);
							break;
						}
						case 2:	{
							graph.setColor(Color.black);
							break;
						}
						case 3:	{
							graph.setColor(Color.red);
							break;
						}
						case 4:	{
							graph.setColor(Color.orange);
							break;
						}
					}
					graph.drawLine(touchUpInfo[i][1],
							i, touchUpInfo[i][2], i);
				}
			}
			
			if (hasRegressionLine) {
				int startX = (int)Math.round(intercept);
				int startY = 0;
				int finX = (int)Math.round((intercept + (slope* 480d)));
				int finY = 480;
				graph.setColor(Color.orange);
				graph.drawLine(startX, startY,finX, finY);
			}
			return inImage;
		}
		//---------------------------------------------
		public BufferedImage textUpImage(BufferedImage inImage, String text) {
			Graphics2D graph = inImage.createGraphics();
			graph.setColor(Color.red);
			graph.drawImage(inImage, 0, 0, null);
			graph.setFont(new Font("Helvetica",Font.BOLD,24));
			graph.drawString(text, 5, 60);
			return inImage;
		}
		//---------------------------------------------------
		public void storeRegressionLine(double intercept, double slope) {
			hasRegressionLine = true;
			this.intercept = intercept;
			this.slope = slope;
		}
}
