# Tutorial 3: SPARQL and the Query Service. This tutorial demonstrates the basics of query
# construct with the aid of the QueryServiceProxy,
# 
# author: Graeme Stevenson (graeme.stevenson@ucd.ie)
#
require 'DataPortProxy'
require 'QueryServiceProxy'

begin
    # Test code from Tutorial 1 to add data to the data store.
    dsProxy = DataPortProxy.new
    
    # Send a VALID piece of RDF to the data store.
    response, message = dsProxy.add "<http://hello><http://construct>\"world\"."
    puts response.to_s + " - CODE: " + message.to_s # message should be AbstractClientProxy::STATUS_OK

    # Create a Query Service Proxy Object
    # The boolean argument "true" indicates connection to localhost only
    qsProxy = QueryServiceProxy.new

    # Construct the SPARQL query.
    query = "SELECT ?subject WHERE{?subject <http://construct> \"world\" .}"
    # Submit the query to construct.
    resultSet = qsProxy.query query

    # Check the result set. Null indicates that an error occured.
    if resultSet != nil
        puts resultSet
    else
        puts "The query did not execute successfully"
    end

rescue Exception => e:
    puts e
end