/**
 * 
 */
package org.construct_infrastructure.main;

import org.construct_infrastructure.bonjourproxy.BonjourProxy;
import org.construct_infrastructure.gui.ConstructGUI;

import com.apple.dnssd.DNSSDException;


/**
 * @author Graeme Stevenson
 */
public class ProxyAndConstructMain {

   /**
    * @param args
    */
   public static void main(String[] args) throws DNSSDException {
      // TODO Auto-generated method stub
      new BonjourProxy();
      final ConstructGUI inst = new ConstructGUI();
      inst.setLocationByPlatform(true);
      inst.setVisible(true);
   }

}
