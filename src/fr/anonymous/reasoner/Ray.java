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



import java.io.Serializable;
import java.util.HashSet;
import java.util.Set;

import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLPropertyExpression;

// a ray of a StarType
// It is necessary to make a copy to change
public class Ray implements Serializable
{
	//The hashCode is not immutable. Therefore, each object should not be changed if it is hashed in a structure
	private int hashcode = 0;
	private RoleLabel ridge; // ridge is the tie
	private ConceptLabel tip; // tip is the tail
//	private Set<OWLIndividual> tipI;

	public Ray() {
		this.ridge = new RoleLabel();
		this.tip  =  new ConceptLabel();
		//	this.tipI=new HashSet();
	}
	/*public void sumCode() 
    {
        hashcode = this.ridge.hashCode() + this.tip.hashCode();
    }*/

	//Creates a ray when we know ids
	public Ray( RoleLabel rl, ConceptLabel tl) {
		this.ridge = new RoleLabel(rl.getRoles());
		this.tip = new ConceptLabel(tl.getConcepts());
		hashcode = sumCode();
	}

	public Ray(Set<OWLPropertyExpression> rs, Set<OWLClassExpression>  cs) {
		this.ridge = new RoleLabel(rs);
		this.tip = new ConceptLabel(cs);
		hashcode = sumCode();
	}

	public Ray(Set<OWLPropertyExpression> rs, Set<OWLClassExpression>  cs, ReasoningData d) {
		this.ridge = new RoleLabel(rs, d);
		this.tip = new ConceptLabel(cs);
		hashcode = sumCode();
	}

	public void addRoles(Set<OWLPropertyExpression> rs)
	{
		this.ridge.addAll(rs);
		hashcode = sumCode();
	}

	public void addConcepts(Set<OWLClassExpression> cs)
	{
		this.tip.addAll(cs);
		hashcode = sumCode();
	}
	//Returns a new ray if "r", "r" is a role and stores the new ridge in the set "ridge" 
	public Ray getNewRayByRole(OWLPropertyExpression r, Set<RoleLabel> ridge , ReasoningData data) {
		RoleLabel rl =  this.ridge.getNewRoleLabel(r, data);
		Ray rr = new Ray(rl, this.tip);
		return rr;
	}

	//Stores the new ridge in the set "ridge"
	public Ray getNewRayByRole(Set<OWLPropertyExpression> roleList, Set<RoleLabel> ridge, ReasoningData data) {
		RoleLabel rl = this.ridge.getNewRoleLabel(roleList, data);
		Ray ray = new Ray(rl, new ConceptLabel(this.tip));
		return ray;
	}


	public boolean tipContains(OWLClassExpression concept){
		if (this.tip.contains(concept))
			return true;
		else return false;
	}

	public boolean containsAll(Ray ray){
		if(this.tip.containsAll( ray.getTip() ) &&
				this.ridge.containsAll(  ray.getRidge() ))
			return true;
		else
			return false;
	}


	/*public void addNNFToTip(ReasoningData data) {
		this.tip.getConcepts().addAll( data.getAllAxiomNNFCore().getConcepts() );     
		hashcode = this.ridge.hashCode() + this.tip.hashCode(); 
	}*/

	public boolean isInverseOf(ConceptLabel core1, ConceptLabel core2, Ray ray ) {
		if ( ! core1.equals( ray.getTip()  ) )
			return false;
		if ( ! this.tip.equals(  core2 ) )
			return false;
		if ( ! this.ridge.isInverseOf( ray.getRidge())  )
			return false;
		else
			return true;
	}

	public RoleLabel getRidge() {
		return ridge;
	}
	public void setRidge(RoleLabel rl) {
		ridge = rl;
		hashcode = sumCode();
	}

	public ConceptLabel getTip() {
		return tip;
	}


	public void setTip(ConceptLabel cl) {
		tip=cl;
		hashcode = sumCode();
	}
	//not commutative
	public int sumCode()
	{
		long hash= 1234;
		hash += this.ridge.hashCode() * 2;
		hash += this.tip.hashCode() * 3;
		return (int)(hash);
	}
	@Override
	public int hashCode()
	{
		return hashcode;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null )
			return false;
		if (getClass() != obj.getClass())
			return false;

		Ray other = (Ray)obj;
		if ( !this.getRidge().equals(other.getRidge()))
			return false;
		if ( !this.getTip().equals(other.getTip()))
			return false;

		return true;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("hashcode="+hashcode+", Ridge:" + System.getProperty("line.separator"));
		sb.append( ridge.toString() );
		sb.append("] [Hash="+ridge.hashCode()+", ");
		sb.append("Tip:" + System.getProperty("line.separator"));
		if(tip.toString()==null || tip.toString().equals("") )
			sb.append("EMPTY TIP");
		else
			sb.append( tip.toString() );
		return sb.toString();
	}

	/*public Set<OWLIndividual> getTipI() {
		return tipI;
	}

	public void setTipI(Set<OWLIndividual> tipI) {
		this.tipI = tipI;
	}*/
}
