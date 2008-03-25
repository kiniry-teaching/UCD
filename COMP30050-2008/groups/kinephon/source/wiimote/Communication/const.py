"""
    This file contains all the constants and magic numbers
    that are used when communicating with the wiimote.
"""

#User-friendly bluetooth name of the wiimote
WIIMOTE_NAME = "Nintendo RVL-CNT-01"

"Ports, packet headers, and packet size info"
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

