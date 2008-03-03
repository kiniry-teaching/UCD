# $Id: AbstractClientProxy.rb 3625 2007-03-15 12:36:26Z gstevenson $

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

# Client-side proxy object that can talk to a Construct discovery service, find services and
# interact with them.
# 
# Author: Graeme Stevenson (graeme.stevenson@ucd.ie)
#
require 'socket'
require 'SocketWrapper'
require 'Message'
include Socket::Constants

class Service

attr_reader :name, :host, :port
  
  def initialize(name, host, port)
   @name = name
   @host = host
   @port = port
  end
  
  def to_s()
    return @name.to_s + "-" + @host.to_s + ":" + @port.to_s
  end
end

class AbstractClientProxy

  # The port on which the Construct bonjour proxy is running.
  LOCAL_CONSTRUCT_BONJOUR_PROXY_PORT = 3826
  
  #The length of the </serviceComponentDescriptor> tag.
  SERVICE_COMPONENT_DESCRIPTOR_END_TAG_LENGTH = 28

   # The identifier representing an OK status message.
   STATUS_OK = "600"
   
    # The identifier representing an ERROR status message.
    STATUS_ERROR = "610";

   # The identifier representing an UNKNOWN status message.
  STATUS_UNKNOWN = "650";

private

  # Get the service descriptors in a big XML string.
  # Return the XML form of the service descriptors (which could just be
  # &lt;services&gt;&lt;/services&gt; or nil if we are not connected to an instance of
  # Construct
  def getXMLServiceDescriptors() 
    begin
      #socket = TCPsocket.open("localhost", 3826) # open socket
      socket = Socket.new( AF_INET, SOCK_STREAM, 0 )
      sockaddr = Socket.pack_sockaddr_in( 3826, 'localhost' )
      socket.connect( sockaddr )
      descriptor = Message.new(socket).payload()
    rescue
      descriptor = nil # an error occured
    ensure
	socket.close if socket # close socket
    end
  end

    # Get the service descriptors in an Array of ServiceComponentDescovery objects.
    def getServiceDescriptors(the_xmlDescriptors)
      serviceObjects = Array.new
      serviceDescriptors = Array.new
      startPosition = the_xmlDescriptors.index('<servicecomponentdescriptor>')
      while(startPosition) do # Add the XML for each service into the array
         endPosition = the_xmlDescriptors.index('</servicecomponentdescriptor>', startPosition) + SERVICE_COMPONENT_DESCRIPTOR_END_TAG_LENGTH
         serviceDescriptors << the_xmlDescriptors.slice!(startPosition..endPosition) #Slice up the string and add results to the array
         startPosition = the_xmlDescriptors.index('<servicecomponentdescriptor>')
      end

      # Extract the service name, host name, and port
      serviceDescriptors.each{|desc| 
        name = desc.match('<name>[\s\w]+<\/name>').to_s if serviceDescriptors[0]
        host = desc.match('<host>[\s\w.]+<\/host>').to_s if serviceDescriptors[0]
        port = desc.match('<port>[\s\w]+<\/port>').to_s if serviceDescriptors[0]
        name = name.slice(6, name.length() -13) if name
        host = host.slice(6, host.length() -13) if host
        port = port.slice(6, port.length() -13) if port
        # Create a service if all three properties are present
        serviceObjects << Service.new(name, host, port) unless ((name == nil) or (host == nil) or (port == nil))
       }
    return serviceObjects  
  end

  # Iterate through a collection of services looking for a named service.
  # We then try to connect to that service.
  def searchForAndConnectToService(the_services, the_service_name)
    commsSocket = nil
    connected = false
    candidates = the_services.find_all { |service| service.name == the_service_name}
    
    # try to connect to a service until we are sucessful
    candidates.each{|candidate|
    begin
      commsSocket = Socket.new( AF_INET, SOCK_STREAM, 0 )
      sockaddr = Socket.pack_sockaddr_in( candidate.port, candidate.host)
      commsSocket.connect( sockaddr )
      connected = true
    rescue
       puts "Failed to connect: " + candidate.name + " " + candidate.port
    end   
     break if connected
    }
    return commsSocket
  end	

public
  # Obtains a connection to a service and places it in a wrapper.
  def getService(a_service_name)
    wrapper = nil
    desc = getXMLServiceDescriptors()
    if desc
      services = getServiceDescriptors(desc) 
      socket = searchForAndConnectToService(services, a_service_name)
      if socket
        begin
          wrapper = SocketWrapper.new(socket)
        rescue
          puts "Error when creating socket wrapper"
        end
      end    
    else
      raise "Local construct bonjour proxy not running on port 3826"
    end
    return wrapper
 end

end


