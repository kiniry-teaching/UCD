import bluetooth

WIIMOTE_NAME = "Nintendo RVL-CNT-01"
NOT_FOUND = "NF"



def findWiimote():
    #find all bluetooth devices around
    all_devices = __findAllDevices();
    
    #look for a device with matching name
    wiimote_address = __findWiimoteBluetoothAddress(all_devices);
    
    print "Wiimote found."
    return wiimote_address
    
def __findAllDevices():
    #todo
    my_devices = bluetooth.discover_devices(lookup_names = True)
    print "All available devices found."
    return my_devices
    
def __findWiimoteBluetoothAddress(some_bt_devices):
    for device_address, device_name in some_bt_devices:
        print "device found: %s-%s" % (device_name, device_address)
        if device_name == WIIMOTE_NAME:
            print "Wiimote BT address: %s" % (device_address)
            return device_address
    
    #if we didn't find any match
    print "Wiimote BT address: NOT FOUND"
    return "NF"

def establishConnection(a_wiimote_address):
    
    
    #open socket
    
    #
    
    print "Connection established."

def closeConnection():
    #todo
    print "Connection closed."