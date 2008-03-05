from Connection import bt_connection
import Communication

from converter import toBytes
from converter import toString


wiimote_address = bt_connection.find_wiimote()

if (wiimote_address != bt_connection.NOT_FOUND):
    bt_connection.establish_connection(wiimote_address)
    
