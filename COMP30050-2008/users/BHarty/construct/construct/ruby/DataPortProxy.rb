# $Id: DataPortProxy.rb 3625 2007-03-15 12:36:26Z gstevenson $

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

# Client-side proxy object that creates a connection with the DataPort
# Requires the addition of functionality to work with a native Ruby RDF Library
# No suitable candidate exists at the moment (Feb 2007)
# Author: Graeme Stevenson (graeme.stevenson@ucd.ie)
#
require 'AbstractClientProxy'
require 'Protocol'

class DataPortProxy<AbstractClientProxy

DATA_PORT_NAME = "Construct DataPort"

   # Creates and returns a connection to a DataPort.
   # Returns nil if an error occurs or none is available
   def getDataPortConnection() 
      getService(DATA_PORT_NAME)
   end
   
   # Adds some RDF to Construct with a given expiry time.
   # If no expiry time is passed, a default of 5 mins is used.
  def add(some_rdf, an_expiryTime="300000")
     add(some_rdf +  an_expiryTime)
  end

    # Adds some RDF to Construct
  def add(some_rdf) 
    begin
      dataPort = getDataPortConnection()
      if dataPort
        response = dataPort.writeToSocket(Protocol.format(some_rdf, Protocol::RDF_ADD))
        dataPort.close()
        return response == STATUS_OK, response
      else
        return false, "No Data Port could be found"  
      end 
    rescue
      return false, "An error occurred: #{$!}"
    end
  end
end





