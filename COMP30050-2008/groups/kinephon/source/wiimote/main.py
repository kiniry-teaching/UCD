from Connection import btConnection
import Communication

wiimote_address = btConnection.findWiimote()

if (wiimote_address != btConnection.NOT_FOUND):
    btConnection.establishConnection(wiimote_address)
