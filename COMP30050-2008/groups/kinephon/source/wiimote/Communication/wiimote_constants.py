"""Report IDs
    as taken from wiili.org/Wiimote"""
    
"Packets sent to the Wiimote have to have a header"
#universal packet header
PACKET_HEADER = 0x52

"for packets from host to wiimote"
#player LEDs, force feedback
#payload: 1 byte
PLAYER_LEDS = 0x11

#Report type/ID
#payload: 2 bytes
REPORT_ID = 0x12

#IR sensor enable
#payload: 1 byte
IR_SENSOR_ENABLE = 0x13

#Speaker enable
#payload: 1 byte
IR_SENSOR_ENABLE = 0x14

#Controller status
#payload: 1 byte
CONTROLLER_STATUS = 0x15

#Write data
#payload: 21 bytes
WRITE_DATA = 0x16

#Read data
#payload: 6 bytes
READ_DATA = 0x17

#Speaker data
#payload: 21 byte
SPEAKER_DATA = 0x18

