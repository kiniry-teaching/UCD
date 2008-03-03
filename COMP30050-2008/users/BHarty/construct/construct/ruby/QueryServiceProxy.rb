# $Id: QueryServiceProxy.rb 3625 2007-03-15 12:36:26Z gstevenson $

# Copyright (c) 2006, Graeme Stevenson. All rights reserved.
# This file is part of Construct, a context-aware systems platform.
# Copyright (c) 2006, 2007 UCD Dublin. All rights reserved.
#
# Construct is free software; you can redistribute it and/or modify
# it under the terms of the GNU Lesser General Public License as
# published by the Free Software Foundation; either version 2.1 of
# the License, or (at your option) any later version.
#
# Construct is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
# GNU Lesser General Public License for more details.
#
# You should have received a copy of the GNU Lesser General Public
# License along with Construct; if not, write to the Free Software
# Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
# USA
#
# Further information about Construct can be obtained from
# http://www.construct-infrastructure.org

# Client-side proxy object that creates a connection with the QueryService
# Requires the addition of functionality to work with a native Ruby RDF Library
# No suitable candidate exists at the moment (Feb 2007).
# Async Query functionality to be added at a later date.
# Author: Graeme Stevenson (graeme.stevenson@ucd.ie)
#
require 'AbstractClientProxy'

class QueryServiceProxy < AbstractClientProxy

QUERY_SERVICE_NAME = "Construct QueryService"

   # Creates and returns a connection to a QueryService.
   # Returns nil if an error occurs or none is available
   def getQueryServiceConnection() 
      getService(QUERY_SERVICE_NAME)
   end
   

    # Sends a SPARQL query to Construct and returns the
    # resultant RDF. This will be updated to return a ResultSet object
    # when a suitable Ruby RDF library is available.
  def query(a_query) 
      queryService = getQueryServiceConnection()
      if queryService
        response = queryService.writeToSocket(Protocol.format(a_query,
            Protocol::QUERY))
        queryService.close()

        if response[0,5] == "ERROR" or response[0,12] == "UNRECOGNISED"
          return false, response
        else
          return true, response
        end
      else 
        return false, "No Query Service could be found"  
      end  
  end
end






