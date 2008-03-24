import bluetooth
import converter
import time


WIIMOTE_NAME = "Nintendo RVL-CNT-01"
NOT_FOUND = "NF"

##
#I found the two following ports in the output of the spdtool
#on this site:
#http://www.wiili.org/index.php/Wii_bluetooth_specs#spd_info
#All other port numbers that I tried (remembering that L2CAP
#only uses odd numbered ports) either timed out of failed to
#connect completely.
#Even swapping these two ports breaks the whole thing.
#Why? I honestly don't know. :(
##
RECEIVE_PORT_NUMBER = 0x13
SEND_PORT_NUMBER = 0x11

global send_socket
global receive_socket


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
    
    global send_socket
    global receive_socket
    
    #first we have to create and open two sockets
    receive_socket = bluetooth.BluetoothSocket(bluetooth.L2CAP)
    send_socket = bluetooth.BluetoothSocket(bluetooth.L2CAP)

    #and then connect to the wiimote
    receive_socket.connect((a_wiimote_address, RECEIVE_PORT_NUMBER))
    send_socket.connect((a_wiimote_address, SEND_PORT_NUMBER))
    
    print "Connection established."

def receive_data():

    last_time = time.gmtime()
    current_time = last_time
    
    counter = 0
    
    while True:
        counter+=1
        if (counter%10000 == 1):
            fout = open("results.dat", "a")

        try:
            data = receive_socket.recv(23)
        except bluetooth.BluetoothError:
            print "connection closed"
            pass
                
        current_time = time.gmtime()
                
        if len(data):
        #if (len(data) & (current_time[5] != last_time[5])):
            #last_time = current_time
            #print current_time[5]
            #print converter.toBytes(data)
            #print data
            dict_data = converter.toBytes(data)
            
            i = 0
            result = []
            for byte in dict_data:
                if (i>=7):
                    result.append(byte)
                i+=1
            #print result
            fout.write(str(result)+"\n")
    if (counter%10000 == 0):
            fout.close()
    
    print "Receiving finished."
    fout.close()
    
def initialise_ir_camera():
    """
    This isitialisation sequence is based on this
    http://homepage.mac.com/ianrickard/wiimote/wiili_wimote.html#marcan.27s_info
    """
    
    
    
    #First we need to tell the wiimote to start sending data to us
    #SET_REPORT to OUTPUT_WHEN_CHANGED on READ_IR_DATA_ONLY
    string1 = converter.toString((0x52, 0x12, 0x00, 0x33))
    
    #Then we have to turn on the IR camera
    #set IR_ENABLER_1  to CONTINUOUS_OUTPUT
    string2 = converter.toString((0x52, 0x13, 0x04))
    #set IR_ENABLER_2  to CONTINUOUS_OUTPUT
    string3 = converter.toString((0x52, 0x1a, 0x04))
    #send_socket.send(string)
    
    ##
    # Now we need to write to the wiimote memory some information about
    # sensitivity of the sensors. The last memory write sets the wiimote
    # to output specific data format.
    ##
    string4 = converter.toString((0x52, 0x16, 0x04, 0xB0, 0x00, 0x30, 0x01, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00))
    string5 = converter.toString((0x52, 0x16, 0x04, 0xB0, 0x00, 0x06, 0x01, 0x90, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00))
    string6 = converter.toString((0x52, 0x16, 0x04, 0xB0, 0x00, 0x08, 0x01, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00))
    string7 = converter.toString((0x52, 0x16, 0x04, 0xB0, 0x00, 0x1a, 0x01, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00))
    string9 = converter.toString((0x52, 0x16, 0x04, 0xB0, 0x00, 0x33, 0x01, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00))
    
    ##
    # Now that we have all the sequences prepared, we can send them to the 
    # wiimote. However, for some strange reason, we cannot just send them 
    # one after another.If we do that, the wiimote doesn't start outputting 
    # data as it should, because the IR camera is not properly initialised 
    # for some reason. The only way I got it to work was to add a 0.1 second
    # pause between each send. I honestly don't know why this delay works, 
    # it's just a magic number, but it works.
    # My guess would be that the wiimote requires certain amount of time to 
    # write the stuff to memory, so if it gets another request for writing 
    # to memory too soon, the data does not get written properly and so the 
    # initialisation sequence is broken.
    ## 
    send_socket.send(string1)
    time.sleep(0.01)
    send_socket.send(string2)
    time.sleep(0.01)
    send_socket.send(string3)
    time.sleep(0.01)
    send_socket.send(string4)
    time.sleep(0.01)
    send_socket.send(string5)
    time.sleep(0.01)
    send_socket.send(string6)
    time.sleep(0.01)
    send_socket.send(string7)
    time.sleep(0.01)
    send_socket.send(string9)
    
    print "IR camera initialised"
    

def close_connection():
    global send_socket
    global receive_socket
    
    send_socket.close()
    receive_socket.close()
    
    print "Connection closed."