#!/bin/sh
# Date: 02/10/2006
# Setup classpath for Construct
# AUTHOR: Lorcan Coyle
# MODIFIED: Graeme Stevenson (23/01/2008)

# All paths are relative to the root directory of Construct
CONSTRUCT_HOME=.
CONSTRUCT_LIB=$CONSTRUCT_HOME/lib
OLDCLASSPATH=$CLASSPATH
export CLASSPATH=$CONSTRUCT_HOME/construct.jar:$CONSTRUCT_LIB/antlr-2.7.5.jar:$CONSTRUCT_LIB/arq.jar:$CONSTRUCT_LIB/arq-extra.jar:$CONSTRUCT_LIB/commons-logging-1.1.jar:$CONSTRUCT_LIB/looks-1.3.2.jar:$CONSTRUCT_LIB/icu4j_3_4.jar:$CONSTRUCT_LIB/construct_images.jar:$CONSTRUCT_LIB/log4j-1.2.12.jar:$CONSTRUCT_LIB/xercesImpl.jar:$CONSTRUCT_LIB/xstream-1.2.jar:$CONSTRUCT_LIB/xpp3_min-1.1.3.4.O.jar:$CONSTRUCT_LIB/concurrent.jar:$CONSTRUCT_LIB/jena.jar:$CONSTRUCT_LIB/stax-api-1.0.jar:$CONSTRUCT_LIB/wstx-asl-3.0.0.jar:$CONSTRUCT_LIB/xml-apis.jar:$CONSTRUCT_LIB/iri.jar:$CONSTRUCT_LIB/jakarta-oro-2.0.5.jar:$CONSTRUCT_LIB/jenatest.jar:$CONSTRUCT_LIB/json.jar:$CONSTRUCT_LIB/hsqldb.jar:$CONSTRUCT_LIB/dns_sd.jar:$CONSTRUCT_LIB/commons-lang-2.2.jar

# Ensure your java.library.path includes jdns_lib. 
# Uncomment and alter as required by your setup
# LD_LIBRARY_PATH=~/mDNSResponder-107.6/mDNSPosix/build/prod/:$CONSTRUCT_LIB
# export LD_LIBRARY_PATH

# Run Construct
java org.construct_infrastructure.main.ProxyAndConstructMain

# replace old classpath
export CLASSPATH=$OLDCLASSPATH
