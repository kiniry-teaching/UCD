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

import com.hp.hpl.jena.rdf.model.Property;
import com.hp.hpl.jena.rdf.model.RDFNode;
import com.hp.hpl.jena.rdf.model.Resource;
import com.hp.hpl.jena.rdf.model.SimpleSelector;
import com.hp.hpl.jena.rdf.model.Statement;

/**
 * This class will select the system meta data statements from the model associated with a
 * given uniqueID.
 * 
 * @author Graeme Stevenson (graeme.stevenson@ucd.ie)
 */

public class MetaDataSelector extends SimpleSelector {
   /**
    * The uniqueID associated with the statements we wish to select.
    */
   private final String my_uniqueID;

   /**
    * Creates a new data selector object which operates over the given properties. A model may
    * restrict statements that are tested to those whose subject matches the subject parameter,
    * whose predicate matches the predicate parameter and whose object matches the object
    * paramater. Any null parameter is considered to match anything. The uniqueID parameter is
    * used to identify all statemnts associated with a particular ID.
    * 
    * @param a_subject
    *           if not null, the subject of selected statements must equal this argument.
    * @param a_predicate
    *           if not null, the subject of selected statements must equal this argument.
    * @param an_object
    *           if not null, the subject of selected statements must equal this argument.
    */
   public MetaDataSelector(final Resource a_subject, final Property a_predicate,
         final RDFNode an_object) {
      super(null, null, (RDFNode) null);
      my_uniqueID = (a_subject.toString() + "@" + a_predicate.toString() + "@" + an_object
            .toString()).replace('#', '$');
   }

   /**
    * Selects any meta data statement associated with the uniqueID.
    * 
    * @param a_statement
    *           A statement to be assessed against the data selector criteria.
    * @return true if the statement is associated with the uniqueID, false otherwise.
    */
   public final boolean selects(final Statement a_statement) {
      return a_statement.getSubject().toString().endsWith(my_uniqueID);
   }
}
