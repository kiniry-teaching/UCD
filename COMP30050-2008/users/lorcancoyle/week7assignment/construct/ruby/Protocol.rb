# $Id: Protocol.rb 3633 2007-05-10 09:51:32Z gstevenson $

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

#
# This class contains utility methods for dealing with the construct protocols.
# 
# Author: Graeme Stevenson (graeme.stevenson@ucd.ie)
#
#require 'Singleton'

class Protocol
	#include Singleton
	
  # The number of bytes in a message code identifier.
  MESSAGE_ID_LENGTH = 3

  # The number of bytes in the payload length descriptor.
  PAYLOAD_SIZE_DESCRIPTOR_LENGTH = 10
 	
  # The protocol identifier for querying.
  QUERY = "200"

  #The protocol identifier used for responding to queries.
  QUERY_RESPONSE = "210"
  
  # The protocol identifier used for sending rdf statements to the data port.
  RDF_ADD = "100"

  # The protocol identifier used for responding to an add rdf statements request.
  RDF_ADD_RESPONSE = "150"

  #The protocol identifier used for sending a service descriptor.
  SERVICE_DESCRIPTOR_RESPONSE = "310"
  
  # An array containing all the protocol identifiers. If you add a new protocol then it must
  # be in this list. This array is used to check incoming format requests to make sure the
  # given code is valid. 
  ALL_PROTOCOL_IDENTIFIERS = [QUERY, QUERY_RESPONSE, RDF_ADD,
						RDF_ADD_RESPONSE, 
						SERVICE_DESCRIPTOR_RESPONSE]

    # A private constructor that exists to defeat instantiation.
 def initialize()
    # Exists to defeat instantiation.
  end
   

  # Encodes a String in preperation for transmition using a given protocol. This method takes
  # the data and code, checks that the code is valid and then returns a new String of the
  # form "&lt;CODE&gt; DATA_PAYLOAD_SIZE_IN_BYTES DATA". Note that the two spaces delimit the
  # three parts of the message.
  # some_data - The data to encoded.
  # a_code - the code representing the protocol ID.
  # returns the encoded String or nil if the code is invalid or format fails.
 def Protocol.format(some_data, a_code)
    codeIsValid = false
    ALL_PROTOCOL_IDENTIFIERS.each{ |identifier|
    codeIsValid = true if identifier == a_code
    break if codeIsValid;
    }
    if codeIsValid
      if not some_data or (some_data.length == 0)
        raise ArgumentError, "No data to be formatted"
      else
       return a_code + paddedLength(some_data) + some_data
      end
    else
      raise ArgumentError, "Invalid protocol code"
    end
  end
  
    # Creates the 10 bytes containing the length of the payload.
  def Protocol.paddedLength(some_data) 
    result = "0000000000"
    if some_data
         len = some_data.length().to_s()
    else
         raise ArgumentError, "null value for the data string"
    end
      return result[0, result.length() - len.length()] + len
  end
  
end
