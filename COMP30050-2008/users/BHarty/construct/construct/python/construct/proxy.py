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

from constructservice import constructService, discoveryService, ServiceError

class proxy:

    LOCAL_CONSTRUCT_BONJOUR_PROXY_PORT = 3826
  
    def __init__(self, contact=None):
        """ Initialises the proxy. 
  If there is a contact passed in this will be the contact that is used when searching for a Construct Proxy.
  If this is None we will try to connect to localhost."""
        if(contact):
            self.contact = contact
        else:
            # set up listener here
            self.contact = ("localhost", self.LOCAL_CONSTRUCT_BONJOUR_PROXY_PORT)
        self.dataport = None
        self.queryservice = None
  
    def __getDataport(self):
        """ Returns the Dataport """
        # is this dataport active?
        if(self.dataport): return self.dataport
        # if not then get a new instance
        self.dataport = self.__getService(constructService.DATAPORT)
        return self.dataport
	
    def __getQueryservice(self):
        """ Returns the Query Service """
        # is this dataport active?
        if(self.queryservice):
            return self.queryservice
        # if not then get a new instance
        self.queryservice = self.__getService(constructService.QUERYSERVICE)
        return self.queryservice
		
    def __getService(self, serviceName):
        """Attempts to connect to a service with the name specified."""

        # TODO LORCAN put a delay in here?
        if(not self.contact):
            raise ServiceError("No Proxy Service Available - nowhere to find it.")
    
        # Now get the queryservice or dataport from this contact  
        discovery = discoveryService(self.contact)  
        if(serviceName == constructService.DATAPORT):
            service = discovery.getDataportService()
            #print "Found service ", service
            return service
        elif(serviceName == constructService.QUERYSERVICE):
            service = discovery.getQueryserviceService()
            #print "Found service ", service
            return service
        else:
            print "ERROR - unknown service name ", serviceName
   
    def insert(self, data):
        """ Attempts to send data via the proxy to Construct"""
        # Get an available dataport
        dataport = self.__getDataport()
        if(not dataport):
            return
        # Got dataport, now send it the data
        return dataport.insert(data)
    
    def query(self, query):
        """ Attempts to send a SPARQL query via the proxy to Construct."""
        # Check if there is an available queryservice
        queryservice = self.__getQueryservice()
        if(not queryservice):
            return
        # Got queryservice, now send it the query
        return queryservice.query(query)

    def close(self):
        if(self.dataport):
            self.dataport.close()
        if(self.queryservice):
            self.queryservice.close()
