package fr.anonymous.reasoner;

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


import java.util.HashSet;
import java.util.Set;

import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;
/**
 * Evolved representation of axioms concerning classes. Splits it in two parts;
 * the part on the left is a class, the part on the right is an expression (both
 * are registered as OWLClassExpressions, for convenience). Both parts are
 * separated by a subset operator.
 * 
 * @author Jeremy Lhez
 * 
 */
public class ConceptAxiom {
	private final OWLClassExpression left;
	private final OWLClassExpression right;
	private final OWLClassExpression NNF;
        private static final OWLDataFactory factory = new OWLDataFactoryImpl();
        
	public ConceptAxiom(OWLClassExpression l, OWLClassExpression r) {
		this.left = l;
		this.right = r;
		OWLClassExpression notL = factory.getOWLObjectComplementOf(l).getNNF();
		Set<OWLClassExpression> clsSet = new HashSet<>();
		clsSet.add( r );
		clsSet.add( notL );
		NNF = factory.getOWLObjectUnionOf(clsSet);
	}

	 
	public OWLClassExpression getLeftMember() {
		return left;
	}

	 
	public OWLClassExpression getRightMember() {
		return right;
	}

	 
	public OWLClassExpression getNNF() {
		return NNF;
	}
	
        @Override
        public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null )
			return false;
		if (getClass() != obj.getClass())
			return false;
		ConceptAxiom other = (ConceptAxiom) obj;
		if( !this.getLeftMember().equals(other.getLeftMember()) )
		    return false;
			return this.getRightMember().equals(other.getRightMember());
		}
}
