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

from rdflib import RDF, Namespace, Literal
from rdflib.Graph import ConjunctiveGraph
FOAF = Namespace("http://xmlns.com/foaf/0.1/")
exampleNS = Namespace("http://www.example.com/")
	
#Create a new Proxy object.
proxy = proxy()
print "Executing Script"
try:
    # Generate a piece of FOAF RDF
    store = ConjunctiveGraph()
    store.bind("foaf", "http://xmlns.com/foaf/0.1/")
    store.add((exampleNS["~joebloggs"], RDF.type, FOAF["Person"]))
    store.add((exampleNS["~joebloggs"], FOAF["name"], Literal("Joe Bloggs")))
    store.add((exampleNS["~joebloggs"], FOAF["nick"], Literal("joe")))
    store.add((exampleNS["~joebloggs"], FOAF["givenname"], Literal("Joe")))
    store.add((exampleNS["~joebloggs"], FOAF["family_name"], Literal("Bloggs")))
    data = store.serialize(format="nt")
    #Send the FOAF RDF to the data store
    if proxy.insert(data):
        print "The following data were added correctly:"
        print data
    else:
        print "Problem encountered when adding the following data:"
        print data
except ServiceError, e:
    print e
# Close the proxy.
proxy.close()