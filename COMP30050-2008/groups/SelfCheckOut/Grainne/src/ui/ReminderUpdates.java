package ui;

import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;

public class ReminderUpdates extends Interface implements ItemListener
{
	
	static final long serialVersionUID=0;
	
	/*
	 * This class updates the customers personal reminder list which 
	 * they created on the customer services web site.
	 */
	
	/*
	 * Requests the reminder list from the Reminder Manager
	 */
	public String[] getReminders()
	{
		remindersList = new String[10];
		remindersList = MessageManager.getUserList(customerNr);
		return remindersList;
		
	}
	
	/*
	 * Here the customer selects items that they no longer need to be
	 * reminded about and therefore creating s new reminders list
	 */
	
	
	public void itemStateChanged(ItemEvent e) 
	{
		for(int i=0;i<remindersList.length;i++)
		{
		 
			if(e.getItem() == reminderChecks[0])
			{
				int updatedReminderListLength = 0;
				updatedRemindersList[updatedReminderListLength] = remindersList[i];
				updatedReminderListLength++;
			}
		}
	}
	

}
