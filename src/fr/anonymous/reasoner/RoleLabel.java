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


 
import java.io.PrintWriter;
import java.io.Serializable;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

//import uk.ac.manchester.cs.owl.owlapi.mansyntaxrenderer.ManchesterOWLSyntaxOWLObjectRendererImpl;
import org.semanticweb.owlapi.model.OWLDataPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLPropertyExpression;

import com.google.common.collect.Sets;
import uk.ac.manchester.cs.owl.owlapi.mansyntaxrenderer.ManchesterOWLSyntaxOWLObjectRendererImpl;

//a set of roles
public class RoleLabel implements Serializable
{
	//private static final int hashcode = 1;
	//The hashCode is not immutable. Therefore, each object should not be changed if it is hashed in a structure
	private int hashcode = 0;
	private Set<OWLPropertyExpression> roles;
           
	public RoleLabel() {
		this.roles = new HashSet<OWLPropertyExpression>();
	}
	
	public RoleLabel(RoleLabel rl) 
	{
	    this.roles = new HashSet<OWLPropertyExpression>( rl.getRoles() );
	    hashcode = sumCode();
	}
	
	public RoleLabel(Set<OWLPropertyExpression> rs) 
	{
		this.roles = new HashSet<OWLPropertyExpression>(rs);	 
		hashcode = sumCode();
	}
	
	public RoleLabel(Set<OWLPropertyExpression> rs, ReasoningData data) 
	{
	  Set<OWLPropertyExpression> rss1 = new HashSet<OWLPropertyExpression>(rs);
	  for(OWLPropertyExpression r : rs)
	  {
		rss1.addAll(data.getSuperClosureByRole().get(r));
	  }
	  this.roles = new HashSet<OWLPropertyExpression>(rss1);
	  for(OWLPropertyExpression r : rss1)
	  {		
		this.roles.addAll(data.getSuperClosureByRole().get(r));  
		/*if(r instanceof OWLObjectPropertyExpression)
		{
		  for(OWLPropertyExpression i : data.getSuperClosureByRole().get(((OWLObjectPropertyExpression)r).getInverseProperty()))
			this.roles.add(((OWLObjectPropertyExpression)i).getInverseProperty());
		}*/  
	  }
	  hashcode = sumCode();
	}
	
	//create a RoleLabel from a single role that must be identified 
	public RoleLabel(OWLPropertyExpression r, ReasoningData data) 
	{
	  Set<OWLPropertyExpression> rs = new HashSet<OWLPropertyExpression>();
	  rs.add(r); 
	  rs.addAll(data.getSuperClosureByRole().get(r));
	  this.roles = new HashSet<OWLPropertyExpression>(rs);
	  for(OWLPropertyExpression i : rs)
	  {
		this.roles.addAll(data.getSuperClosureByRole().get(r));
	    /*if(i instanceof OWLObjectPropertyExpression)
	    {
		 for(OWLPropertyExpression j : data.getSuperClosureByRole().get(((OWLObjectPropertyExpression)i).getInverseProperty()))
		   this.roles.add(((OWLObjectPropertyExpression)i).getInverseProperty());
	    }*/
	  }
	  hashcode = sumCode();
	}
	 
	//It changes this object
	public void add(OWLPropertyExpression r) 
	{
		roles.add(r);
		hashcode = sumCode();
	}
	
	public void addAll(Set<OWLPropertyExpression> rs) 
	{
		roles.addAll(rs);
		hashcode = sumCode();
	}
	 
	//If "r" is not in "this", a new RoleLabel is created 
  public  RoleLabel getNewRoleLabel(OWLPropertyExpression r, ReasoningData data) 
  {
	if(!this.contains(r) ) 
	{
	  return new RoleLabel(Sets.union(Collections.singleton(r), Sets.union(this.roles, data.getSuperClosureByRole().get(r))));  
    } else
	  return this;
  }

  public  RoleLabel getNewRoleLabel(Set<OWLPropertyExpression> lr, ReasoningData data) 
  {
	Set<OWLPropertyExpression> rr = new HashSet<OWLPropertyExpression>(this.roles);
	for(OWLPropertyExpression i : lr) 
	{
	  rr.add(i);
	  rr.addAll(data.getSuperClosureByRole().get(i));
		   
	}	 
    return new RoleLabel(rr);  
		 
  }
	
	 

  public  boolean containsAll(RoleLabel rl) 
  {
		return roles.containsAll(rl.getRoles());
  }
	
	public  boolean contains(OWLPropertyExpression role) {
		return roles.contains(role);
	}

	 

  public boolean isInverseOf(RoleLabel roleLabel) 
  {    
	for(OWLPropertyExpression r : roleLabel.getRoles())
	  if(r.isDataPropertyExpression())
	    return false;
	return this.equals(roleLabel.getInverseOf());
  }

	public void setRoles(Set<OWLPropertyExpression> s) {
		this.roles = s;
		hashcode = sumCode();
	}

	public Set<OWLPropertyExpression> getRoles() {
		return this.roles;
	}
	
  public RoleLabel getInverseOf() 
  {
	Set<OWLPropertyExpression> rr = new HashSet<OWLPropertyExpression>();
	for(OWLPropertyExpression r : this.roles) 
	{
	  //It is not possible to get inverse of a data role
	  if((r instanceof OWLDataPropertyExpression) )
	      return this; 
	  rr.add(((OWLObjectPropertyExpression)r).getInverseProperty());
	}
	RoleLabel rl = new RoleLabel(rr);
	return rl;
  }
   /*
    * commutative  
    */
   public int sumCode() 
   {
	 long hash= 1234;
	 for(OWLPropertyExpression c : this.roles) 
	 {	 
		  hash += c.hashCode();  
	 }
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
			
		RoleLabel other = (RoleLabel) obj;
		//Check if two sets of identifiers equal. This is performed between two sets of Integers 
		if( !this.getRoles().equals(other.getRoles()) )  
		     return false;
 
		return true;
	}

	public String toSimpleString( ) 
	{
		ManchesterOWLSyntaxOWLObjectRendererImpl render = new ManchesterOWLSyntaxOWLObjectRendererImpl();
		String s = "[ ";
		for (OWLPropertyExpression co : roles) {
			 
			s = s + render.render(co) + "," ;
			 
		}
		s=s+"]";
		return s;
	}
	public void toXML( PrintWriter writer ) {
		writer.print("[");
		ManchesterOWLSyntaxOWLObjectRendererImpl render = new ManchesterOWLSyntaxOWLObjectRendererImpl();
		for (OWLPropertyExpression co : roles) {
			
			writer.print(render.render(co) +",");
			 
		}
		writer.print("]");
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		ManchesterOWLSyntaxOWLObjectRendererImpl render = new ManchesterOWLSyntaxOWLObjectRendererImpl();
		//sb.append(  + System.getProperty("line.separator"));
		if(roles.isEmpty()) {
		   sb.append("EMPTY\n");
		   return sb.toString();
		}
		sb.append("hashcode= "+hashcode+", ");
		for (OWLPropertyExpression r : roles) {
			sb.append( render.render(r) + ", ");
		}

		return sb.toString();
	}
}
