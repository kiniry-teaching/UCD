#
# Tutorial 1: Sending an RDF statement to the Data Port. This tutorial shows the basics of
# connecting to Construct using Ruby.
# 
# author: Graeme Stevenson (graeme.stevenson@ucd.ie)
#
require 'DataPortProxy'

begin
    # Create a new DataPortProxy object.
    # The boolean argument "true" indicates that we want to connect to Construct running
    # on the localhost only.
    proxy = DataPortProxy.new
    # Send a VALID piece of RDF to the data store
    # The proxy code handles all interaction with bonjour and will return null after a
    # timeout of 10 seconds if nothing can be located.
   response, message = proxy.add "<http://hello><http://construct>\"world\"."
   puts response.to_s + " - CODE: " + message.to_s # message should be AbstractClientProxy::STATUS_OK

    # Send an INVALID piece of RDF to the data store;
   response, message = proxy.add "<http://badly><http://formed>\"rd\"f\"."
   puts response.to_s + " - CODE: " + message.to_s   # message should be AbstractClientProxy::STATUS_ERROR

 rescue Exception => e:
    # Thrown if we cannot find a Data Port.
    puts e
end