/*
 * $Id$
 *
 * Copyright (C) Paris8-Paris13, 2013-2021
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 2.1 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA
 */

package fr.anonymous.reasoner;
import java.io.Serializable;
import java.util.HashSet;
import java.util.Set;

import org.semanticweb.owlapi.model.OWLClassExpression;

public class BinaryLabel  implements Serializable {
	//private static final int ID = 1;
	//The hashCode is not immutable. Therefore, each object should not be changed if it is hashed in a structure
    private final int ID;
	// This set contains also nominal
	private Set<OWLClassExpression> both;
	
	 
	public BinaryLabel() {
		both = new HashSet<OWLClassExpression>();
		ID = 0;	 
	}
	
	
	public BinaryLabel(OWLClassExpression c1, OWLClassExpression c2) {
	       both = new HashSet<OWLClassExpression>();
	       both.add(c1);
	       both.add(c2);
	       ID = c1.hashCode() + c2.hashCode(); 	 
	}
	
	public BinaryLabel(OWLClassExpression c1 ) {
	       both = new HashSet<OWLClassExpression>();
	       both.add(c1);
	       
	       ID = c1.hashCode()  ; 	 
	}
	
	public BinaryLabel(Set<OWLClassExpression> cs ) {
	       both = new HashSet<OWLClassExpression>(cs);
	       Object[] arr = cs.toArray();
	       
	       ID = ((OWLClassExpression)arr[0]).hashCode() + ((OWLClassExpression)arr[1]).hashCode(); 	 
	}
	
	public BinaryLabel(BinaryLabel cl) 
	{
	       both = new HashSet<OWLClassExpression>( cl.getBoth() );
	       ID = cl.hashCode(); 
	}

	public Set<OWLClassExpression> getBoth() {
	       return this.both;
	}
	 
	
	 
	
	@Override
        public int hashCode() {
		return ID;
        }
	 

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null )
			return false;
		if (getClass() != obj.getClass())
			return false;
		BinaryLabel other = (BinaryLabel) obj;
		
		if( !this.getBoth().equals(other.getBoth() )  )
		     return false;

		return true;
	}

	 
}
