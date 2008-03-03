//
// $Revision: 7373 $: $Date: 2008-01-24 11:20:18 +0000 (Thu, 24 Jan 2008) $ - $Author: gstevenson $
//
//  This file is part of Construct, a context-aware systems platform.
//  Copyright (c) 2006, 2007, 2008 UCD Dublin. All rights reserved.
// 
//  Construct is free software; you can redistribute it and/or modify
//  it under the terms of the GNU Lesser General Public License as
//  published by the Free Software Foundation; either version 2.1 of
//  the License, or (at your option) any later version.
// 
//  Construct is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
//  GNU Lesser General Public License for more details.
// 
//  You should have received a copy of the GNU Lesser General Public
//  License along with Construct; if not, write to the Free Software
//  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
//  USA
//
//  Further information about Construct can be obtained from
//  http://www.construct-infrastructure.org
package org.construct_infrastructure.component.datastorage;

import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.ModelFactory;
import com.hp.hpl.jena.rdf.model.Property;

/**
 * Class representing the statement seta data used by the system.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */
public final class MetaData {

   /**
    * The Prefix for Meta Data Subjects.
    */
   public static final String SUBJECT_PREFIX = "http://construct/stmt/";
   
   /**
    * The URI containing the ontology represented by this object.
    */
   public static final String PREDICATE_URI = "http://construct/rdfstatementmetadata#";

   /**
    * A Jena model, used to create new Property objects.
    */
   private static Model model = ModelFactory.createDefaultModel();
   
   /**
    * The property representing the time a statement will expire.
    */
   public static final Property EXPIRY_COUNTDOWN = model.createProperty(PREDICATE_URI, 
         "expiryCountdown");

   /**
    * Exists to defeat instantiation.
    */
   private MetaData() {
      super();
      // Does nothing
   }

}
