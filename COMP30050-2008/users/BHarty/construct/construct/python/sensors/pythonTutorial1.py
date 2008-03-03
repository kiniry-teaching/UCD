"""This file is part of Construct, a context-aware systems platform.
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
from construct.proxy import proxy
from construct.constructservice import ServiceError
# Create a new Proxy object. 
proxy = proxy()
print "Executing Script"
try:
	# Send a VALID piece of RDF to the data store
    insertGoodResponse = proxy.insert("<http://hello><http://construct>\"world\".")
    print "Response to good RDF: " + str(insertGoodResponse) 
    # response should be "1"
	#Send an INVALID piece of RDF to the data store
    insertBadResponse = proxy.insert("<http://badly><http://formed>\"rd\"f\".")
    print "Response to bad RDF: " + str(insertBadResponse) 
    # response should be "None"
except ServiceError, e:
    print e.value
#Close the proxy.
proxy.close()