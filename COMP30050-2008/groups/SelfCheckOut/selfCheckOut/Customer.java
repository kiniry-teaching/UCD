package selfCheckOut;
/*@author deirdre power
 * **/
public class Customer {
	private int idNumber;
	private String customerName;
	private String customerEmail;
	
	public Customer(int number, String name, String email){
		idNumber = number;
		customerName = name;
		customerEmail = email;
	}
	public int getIdNumber(){
		return idNumber;
	}
	
	public String getCustomerName(){
		return customerName;
	}
	
	public String getCustomerEmail(){
		return customerEmail;
	}
}
