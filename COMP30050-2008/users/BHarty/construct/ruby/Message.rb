# $Id: Message.rb 3615 2007-03-09 10:14:49Z gstevenson $

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
# This class takes an input stream and attempt to obtain a (single) valid message from it. If
# an exception does not occur, the caller can assume that the message is valid. This class
# does not deal with closing streams.
# 
# Author: Graeme Stevenson (graeme.stevenson@ucd.ie)
require 'Protocol'

class Message

attr_reader :message_id, :payload_length, :payload

  #Read a message from an input stream
  def initialize(a_socket)
      # Read the messageID
      @message_id = a_socket.recvfrom(3)[0] 
      raise "Error reading message identifier. Stream too short" unless @message_id.length == Protocol::MESSAGE_ID_LENGTH
    # Read the payload length
      @payload_length = a_socket.recvfrom(10)[0] 
      raise "Error reading payload length. Stream too short" unless @payload_length.length == Protocol::PAYLOAD_SIZE_DESCRIPTOR_LENGTH
      @payload_length = @payload_length.to_i
      # Read the payload
      @payload = a_socket.recvfrom(@payload_length)[0] 
      raise "Error reading payload stream. Stream too short" unless @payload.length == @payload_length  
  end
end

