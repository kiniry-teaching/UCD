from Connection import bt_connection

wiimote_address = bt_connection.find_wiimote()

if (wiimote_address != bt_connection.NOT_FOUND):
    bt_connection.establish_connection(wiimote_address)
    bt_connection.initialise_ir_camera()
    bt_connection.receive_data()
    bt_connection.close_connection()
    print "transmission complete"
else:
    print "transmission failed: wiimote not found"


    
    
