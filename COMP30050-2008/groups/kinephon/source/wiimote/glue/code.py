import time
import bluetooth
from struct import unpack
from struct import pack

#User-friendly bluetooth name of the wiimote
WIIMOTE_NAME = "Nintendo RVL-CNT-01"
NOT_FOUND = "NOT_FOUND"

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

#Packets sent to the Wiimote have to have this header.
#universal packet header
PACKET_HEADER = 0x52

#The maximum size that a packet sent fromthe wiimote can 
#possibly have
MAX_PACKET_SIZE = 23


"Report IDs"
#Report type/ID
#payload: 2 bytes
SET_REPORT = 0x12

#IR sensor enable
#payload: 1 byte
IR_SENSOR_ENABLER_1 = 0x13

#Speaker enable
#payload: 1 byte
IR_SENSOR_ENABLER_2 = 0x1a

#Write data
#payload: 21 bytes
WRITE_DATA_TO_MEMORY = 0x16

#Report channel for accelerometer and IR data
REPORT_ACC_IR = 0x33


"Report settings"
#Output only when a change in state occurs
OUTPUT_WHEN_CHANGED = 0x00

#Output continuously
OUTPUT_CONTINUOUSLY = 0x04




#Turns a string into a list of byte values.
def toBytes(a_string):
    return unpack('%sB' % len(a_string), a_string)

#Turns a list of byte values into a string.
def toString(a_list_of_bytes):
    result = ""
    for byte in a_list_of_bytes:
        bstr = pack('B' , byte)
        result = result+bstr
        
    return result

global send_socket
global receive_socket


def find_wiimote():
    #find all bluetooth devices around
    all_devices = _find_all_devices()
    
    #look for a device with matching name
    wiimote_address = _find_wiimote_bluetooth_address(all_devices)
    
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
    return NOT_FOUND

def establish_connection(wiimote_address):
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
    receive_socket.connect((wiimote_address, RECEIVE_PORT_NUMBER))
    send_socket.connect((wiimote_address, SEND_PORT_NUMBER))
    
    print "Connection established."

def receive_data():    
    send_socket.send(toString((0x52, 0x11, 240)))
    counter = 0
    fout = open("results.dat", "a")
    for n in range(1, 10000):
        counter += 1
        if (counter%1000 == 0):
            print counter

        result = receive_report()
        fout.write(str(result)+"\n")
    
    fout.close()
    print "Receiving finished."
    
def initialise_ir_camera():
    """
    This isitialisation sequence is based on this
    http://homepage.mac.com/ianrickard/wiimote/wiili_wimote.html#marcan.27s_info
    """
    
    
    
    #First we need to tell the wiimote to start sending data to us
    #SET_REPORT to OUTPUT_WHEN_CHANGED on READ_IR_DATA_ONLY
    string1 = toString((PACKET_HEADER, SET_REPORT, OUTPUT_WHEN_CHANGED, REPORT_ACC_IR))
    
    #Then we have to turn on the IR camera
    #set IR_ENABLER_1  to CONTINUOUS_OUTPUT
    string2 = toString((PACKET_HEADER, IR_SENSOR_ENABLER_1, OUTPUT_CONTINUOUSLY))
    #set IR_ENABLER_2  to CONTINUOUS_OUTPUT
    string3 = toString((PACKET_HEADER, IR_SENSOR_ENABLER_2, OUTPUT_CONTINUOUSLY))
    #send_socket.send(string)
    
    ##
    # Now we need to write to the wiimote memory some information about
    # sensitivity of the sensors. The last memory write sets the wiimote
    # to output specific data format.
    #
    # Note: The format of the memory writes is as follows:
    # packet header (1byte), memory-write report ID (1byte),
    # flags (1byte), memory location (3bytes), data size (1byte),
    # data (16bytes)
    ##
    ##
    # I might have slightly increased the sensitivity of the wiimote byt changing
    # the two lines that are commented out at the moment.
    # source: http://www.wiili.org/index.php/Talk:Wiimote#inio.27s_info
    ##
    string4 = toString((PACKET_HEADER, WRITE_DATA_TO_MEMORY, 0x04, 0xB0, 0x00, 0x30, 0x01, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00))
    string5 = toString((PACKET_HEADER, WRITE_DATA_TO_MEMORY, 0x04, 0xB0, 0x00, 0x06, 0x01, 0x90, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00))
    string6 = toString((PACKET_HEADER, WRITE_DATA_TO_MEMORY, 0x04, 0xB0, 0x00, 0x08, 0x01, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00))
    #string6 = converter.toString((const.PACKET_HEADER, const.WRITE_DATA_TO_MEMORY, 0x04, 0xB0, 0x00, 0x08, 0x41, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00))
    string7 = toString((PACKET_HEADER, WRITE_DATA_TO_MEMORY, 0x04, 0xB0, 0x00, 0x1a, 0x01, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00))
    #string7 = converter.toString((const.PACKET_HEADER, const.WRITE_DATA_TO_MEMORY, 0x04, 0xB0, 0x00, 0x1a, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00))
    string9 = toString((PACKET_HEADER, WRITE_DATA_TO_MEMORY, 0x04, 0xB0, 0x00, 0x33, 0x01, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00))
    
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
    
previous_leds = 0

def receive_report():
    global previous_leds
    try:
        data = receive_socket.recv(MAX_PACKET_SIZE)
    except bluetooth.BluetoothError:
        print "connection closed"
                
    if len(data):
        dict_data = toBytes(data)
            
        i = 0
        result = []
        for byte in dict_data:
            if (i>=7):
                result.append(byte)
            i += 1
            
        #now we will report the points that are visible on the wiimote
        leds = 0
        if (len(result) > 0):
            if (result[0] != 255):
                leds += 16
            if (result[3] != 255):
                leds += 32
            if (result[6] != 255):
                leds += 64
            if (result[9] != 255):
                leds += 128
        if (leds != previous_leds) :
            send_socket.send(toString((0x52, 0x11, leds)))
            previous_leds = leds
            #print leds
        return result
      
def close_connection():
    global send_socket
    global receive_socket
    
    send_socket.close()
    receive_socket.close()
    
    print "Connection closed."
    
#wiimote_address = find_wiimote()
wiimote_address = "00:1E:35:06:74:BD"
print "wiimote search complete"

""" if (wiimote_address != NOT_FOUND):
    print wiimote_address
    establish_connection(wiimote_address)
    initialise_ir_camera()
    receive_data()
    close_connection()
    print "transmission complete"
else:
    print "transmission failed: wiimote not found" """
