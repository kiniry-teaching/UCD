package selfCheckOut.testCode;
import selfCheckOut.Weight;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.ByteArrayOutputStream;
import java.io.ByteArrayInputStream;
import java.util.Arrays;

//http://www.javabeginner.com/object-serialization.htm
//http://www.exampledepot.com/egs/java.io/SerializeObj.html

/*
http://java.sun.com/developer/technicalArticles/ALT/serialization/

*/
public class PersistWeightTest01 {

	
	public static void main(String args[]) {
		Weight myWeight = new Weight(1234);
		ObjectOutputStream oout = null;
		ByteArrayOutputStream baos = null;
		//ByteArrayInputStream byis = null;

		try {
			baos = new ByteArrayOutputStream();
			oout =  new ObjectOutputStream(baos);
			oout.writeObject(myWeight);
			oout.close();
			//oout =  new ObjectOutputStream(baos);
			System.out.println("Object Persisted");
			//System.out.println();
			//System.out.println(baos);
			//System.out.println();
			//System.out.println(baos.toByteArray());
			
		} catch (IOException ex) {
			ex.printStackTrace();
		}
		
		byte[] buf = baos.toByteArray();
		try {
			String bufString = new String(buf,"Cp437");
			//System.out.println(buf);
			//System.out.println();
			//System.out.println("bufString= " + bufString);
			//System.out.println();
      
      
			byte[] buf2 = bufString.getBytes("Cp437");  // convert it back to byte[]
      
      
			System.out.println("ArrayEqual? " + Arrays.equals(buf, buf2) + ", len = " +
					buf2.length  + ", len = " + buf.length);
      
			//for (int i = 0; i < buf.length; i++) {
				//System.out.println("buf = " + buf[i] + ", buf2 = " + buf2[i] + ", i = " + i);
			//}
      
      
      
      
			ObjectInputStream objectIn = new ObjectInputStream(
			new ByteArrayInputStream(buf2));
				
			myWeight = (Weight) objectIn.readObject();
			System.out.println(myWeight.getTimeStamp() + ", " + myWeight.getWeightInt());
			objectIn.close();
		
		} 
		catch (IOException ex) {
			ex.printStackTrace();
		}
		catch (ClassNotFoundException ex) {
			ex.printStackTrace();
		}
		catch (Exception ex) {
			ex.printStackTrace();
		}
	}
}
