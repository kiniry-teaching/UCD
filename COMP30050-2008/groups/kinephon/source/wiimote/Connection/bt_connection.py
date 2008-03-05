import bluetooth
import converter

WIIMOTE_NAME = "Nintendo RVL-CNT-01"
NOT_FOUND = "NF"

RECEIVE_SOCKET_NUMBER = 0x13
SEND_SOCKET_NUMBER = 0x11


def find_wiimote():
    #find all bluetooth devices around
    all_devices = _find_all_devices()
    
    #look for a device with matching name
    wiimote_address = _find_wiimote_bluetooth_address(all_devices)
    
    print "Wiimote found."
    return wiimote_address
    
def _find_all_devices():
    #todo
    my_devices = bluetooth.discover_devices(lookup_names = True)
    print "All available devices found."
    return my_devices
    
def _find_wiimote_bluetooth_address(some_bt_devices):
    for device_address, device_name in some_bt_devices:
        print "device found: %s-%s" % (device_name, device_address)
        if device_name == WIIMOTE_NAME:
            print "Wiimote BT address: %s" % (device_address)
            return device_address
    
    #if we didn't find any match
    print "Wiimote BT address: NOT FOUND"
    return "NF"

def establish_connection(a_wiimote_address):
    """'connect', 'connect_ex', 'close',
        'fileno', 'getpeername', 'getsockname', 'gettimeout',
        'getsockopt', 'listen', 'makefile', 'recv', 'recvfrom', 'sendall',
        'send', 'sendto', 'setblocking', 'setsockopt', 'settimeout', 
        'shutdown'"""
    
    
    #open socket
    receive_socket = bluetooth.BluetoothSocket(bluetooth.L2CAP)
    send_socket = bluetooth.BluetoothSocket(bluetooth.L2CAP)
    
    print "sockets created"
    
    receive_socket.connect((a_wiimote_address, RECEIVE_SOCKET_NUMBER))
    send_socket.connect((a_wiimote_address, SEND_SOCKET_NUMBER))
    
    print "connected"
    string = converter.toString((0x52, 0x15, 0x00))
    
    send_socket.send(string)
    print "sent"
    
    while True:
        try:
            data = receive_socket.recv(23)
            if len(data):
                print "Received:"
                print converter.toBytes(data)
        except bluetooth.BluetoothError:
            print "connection closed"
            pass
        

    receive_socket.close()
    
    
    
    print "over"
    
    
    #
    
    print "Connection established."
    

def close_connection():
    #todo
    print "Connection closed."