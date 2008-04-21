from struct import unpack
from struct import pack

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