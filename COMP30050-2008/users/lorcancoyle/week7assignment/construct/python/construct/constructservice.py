"""Construct client proxy for Python
Author Lorcan Coyle

Copyright (C) 2006, 2007, 2008 Lorcan Coyle
This file is part of Construct, a context-aware systems platform.
Copyright (c) 2006, 2007, 2008 UCD Dublin. All rights reserved.

Construct is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as
published by the Free Software Foundation; either version 2.1 of
the License, or (at your option) any later version.

Construct is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with Construct; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
USA

Further information about Construct can be obtained from
http://www.construct-infrastructure.org
"""
__author__ = "Lorcan Coyle"
import socket
import re

class constructService:
    DATAPORT = "Construct DataPort"
    QUERYSERVICE = "Construct QueryService"
    # Details on the following codes available here: https://secure.ucd.ie/twiki/bin/view/Construct/ConstructFirstPrinciples
	
    # The protocol identifier for querying.
    QUERY = "200"
    
    # The protocol identifier used for responding to queries.
    QUERYRESPONSE = "210"
	
    # The protocol identifier used for sending rdf statements to the data port.
    RDF_ADD = "100"
	
    # The protocol identifier used for responding to an add rdf statements request.
    RDF_ADD_RESPONSE = "110"
	
    # The protocol identifier used for sending a service descriptor.
    SERVICE_DESCRIPTOR_RESPONSE = "310"
	
    # The number of bytes in the payload length descriptor.
    PAYLOAD_DESCRIPTOR_SIZE = 10
	
    """
	# TODO persistent querying has not been implemented yet
	# The protocol identifier for persistent querying.
	PERSISTENT_QUERY = "400";
	# The protocol identifier used for responding to persistent queries.
	PERSISTENT_QUERY_RESPONSE = "410";
	# The protocol identifier for unsubscribing from a persistent querying.
	UNSUB_PERSISTENT_QUERY = "450";"""

    # The identifier representing an OK status message.
    STATUS_OK = "600"
    # The identifier representing an ERROR status message.
    STATUS_ERROR = "610"
    # The identifier representing an UNKNOWN status message.
    STATUS_UNKNOWN = "650"
	
	
    def __init__(self, contact):
        self.my_socket = None
        self.contact = contact
        self.connect(self.contact)

    def connect(self, contact):
        self.my_socket = socket.socket(socket.AF_INET,socket.SOCK_STREAM)
        try:
            self.my_socket.connect(contact)
        except socket.error:
            message = "Error - unable to contact an instance node of Construct (using address " + contact[0] + ":" + str(contact[1]) + "). Is the Construct Proxy running at that address?"
            raise ServiceError(message)
	
    def close(self):
        self.my_socket.close()
		
    def recv_end(self, type):	  	
        REGEXP = re.compile('^('+type+')(\d{'+str(self.PAYLOAD_DESCRIPTOR_SIZE)+'})(.+)', re.DOTALL)
        full_message=""
        data = ''
        try:
            data=self.my_socket.recv(8192)
        except socket.error, e:
            self.connect(self.contact)
            try:
                data=self.my_socket.recv(8192)
            except socket.error, e2:
                pass
            print "Dropped socket connection. Was unable to recover connection",
            print e
            return None
		
        #print "received '" + data + "'"
        correctProtocol = REGEXP.match(data)
        if(correctProtocol):
            message_protocol = correctProtocol.group(1)
            message_length = int(correctProtocol.group(2))
            message = correctProtocol.group(3)
            full_message = message
            #print message_length
            #print "'" + message + "'"
            if len(full_message) > message_length:
                print "WARNING: Short message, short by " + str(len(full_message) - message_length) + " characters: '" + full_message[message_length:] + "'."
                return full_message[0:message_length]
            elif len(full_message) == message_length:
                return full_message
            else:
                while True:         
                    # TODO there may be a problem here if not enough data is returned. This could block indefinitely
                    try:
                        message=self.my_socket.recv(8192)
                    except socket.error, e:
                        self.connect(self.contact)
                        try:
                            message = self.my_socket.recv(8192)
                        except socket.error, e2:
                            pass
                        print "Dropped socket connection. Was unable to recover connection",
                        print e
                        return None
                    if not message:
                        raise ServiceError("Error - socket closed unexpectedly")
                    full_message = full_message + message
                    if len(full_message) == message_length:
                        return full_message
                    elif len(full_message) > message_length:
                        raise ServiceError("Error - expecting Message of length " + message_length + ". Got too much data: " + full_message)
        else:
            error = "Unrecognised Protocol - expecting protocol like \"" + type + "MESSAGE_SIZE MESSAGE\". Got \"" + data + "\""
            raise ServiceError(error)
  
    def sendMessage(self, message, type):
        if(type != constructService.RDF_ADD and type != constructService.QUERY):
            message = "ERROR: processMessageToSend is being expected to process a message of type " + type + ". It is unable to do this."
            raise ServiceError(message)
        length = str(len(message))
        if len(length) > 10:
            raise ServiceError("ERROR - message Length is too long!")
        elif len(length) < 10:
            length = "0000000000" + length
            length = length[-10:]
        processedMessage = type + length + message
        #print "Processed Message -> " + processedMessage
        size = 0
        try:
            size = self.my_socket.send(processedMessage)		
        except socket.error, e:
            self.connect(self.contact)
            try:
                size = self.my_socket.send(processedMessage)
            except socket.error, e2:
                pass
            print "Dropped socket connection. Was unable to recover connection",
            print e
        return size
  
class discoveryService(constructService):
    def __init__(self, contact):
        #self(contact.getHost(), contact.getPort())
        """ Receives response, parses service descriptors """
        constructService.__init__(self, contact)
        #print "connected to construct proxy." + " Host=",contact[0] + ", port=", contact[1]
        self.servicesdescriptions = self.recv_end(constructService.SERVICE_DESCRIPTOR_RESPONSE)
        if(self.servicesdescriptions == "<services></services>"):
            raise ServiceError("Error: No instance of Construct found. Please ensure you are within Zeroconf range of a running instance of Construct")
        #print self.servicesdescriptions
    
    def __repr__(self):
        """String representation"""
        return "<Discovery Service: " + repr(self.contact) + ">"

    def getDataportService(self):
        """ Creates and populates service descriptors"""
        #print "Services Descriptions:", self.servicesdescriptions
        for name,description,host,port,misc in re.findall('<servicecomponentdescriptor>\s*<name>(.+?)</name>\s*<description>(.+?)</description>\s*<host>(.+?)</host>\s*<port>(\d+?)</port>\s*<misc>(.+?)</misc>\s*</servicecomponentdescriptor>', self.servicesdescriptions):
            if(name == 'Construct DataPort'):		
                #dataport['name'] = match[0]
                #dataport['description'] = match[1]
                #dataport['misc'] = match[4]
                contact = (host, int(port))
                #print contact
                return dataportService(contact)
				
    def getQueryserviceService(self):
        """ Creates and populates service descriptors"""
        for name,description,host,port,misc in re.findall('<servicecomponentdescriptor>\s*<name>(.+?)</name>\s*<description>(.+?)</description>\s*<host>(.+?)</host>\s*<port>(\d+?)</port>\s*<misc>(.+?)</misc>\s*</servicecomponentdescriptor>', self.servicesdescriptions):
            if(name == 'Construct QueryService'):		
                #dataport['name'] = match[0]
                #dataport['description'] = match[1]
                #dataport['misc'] = match[4]
                contact = (host, int(port))
                #print contact
                return queryserviceService(contact)

class dataportService(constructService):		
    def __repr__(self):
        """String representation"""
        return "<Dataport Service: " + repr(self.contact) + ">"
		
    def insert(self, data):
        """ Now attempt to open communication with data port"""
        #print "inserting to " + str(self.contact)		
        self.sendMessage(data, constructService.RDF_ADD)
        response = self.recv_end(constructService.RDF_ADD_RESPONSE)
        #print "Response=" + response
        # Was the response ok? if so return 1, otherwise None.
        if(re.match(self.STATUS_OK, response)):
            return 1
        return None

class queryserviceService(constructService):
    def __repr__(self):
        """String representation"""
        return "<Queryservice Service: " + repr(self.contact) + ">"

    def query(self, query):
        """ Now attempt to open communication with query service"""   
        self.sendMessage(query, constructService.QUERY)
        return self.recv_end(constructService.QUERYRESPONSE)
		
class ServiceError(Exception):
    def __init__(self, value):
        self.value = value
        Exception.__init__()
    def __str__(self):
        return repr(self.value)