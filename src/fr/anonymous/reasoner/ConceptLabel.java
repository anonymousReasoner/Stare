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
import java.util.LinkedHashSet;
import java.util.Set;

//import uk.ac.manchester.cs.owl.owlapi.mansyntaxrenderer.ManchesterOWLSyntaxOWLObjectRendererImpl;
//a set of concepts
import org.semanticweb.owlapi.model.ClassExpressionType;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataRange;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectOneOf;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;

import com.google.common.collect.Sets;
import uk.ac.manchester.cs.owl.owlapi.mansyntaxrenderer.ManchesterOWLSyntaxOWLObjectRendererImpl;

public class ConceptLabel implements Serializable
{
	//The hashCode is not immutable. Therefore, each object should not be changed if it is hashed in a structure
  private int hashcode = 0;
	// This set contains also nominal
  private LinkedHashSet<OWLClassExpression> concepts; //this set contains also nominals
	// Each concept nominal contains a set of individuals considered as union 
	// For instance, if {a,b} is contained in a ConceptLabel then either a or b (or both) is contained 
	// in that ConceptLabel 
 	//private Set<OWLObjectOneOf> nominals; 
  private OWLDataRange dataRange = null; // Datatypes are disjoints
    //private int counter = 0;
  private Set<OWLIndividual> individuals;
  
  /*
   * It may contain a nominal concepts as disjunction
   */
  public boolean isNominal()
  {
	for(OWLClassExpression c : concepts)
	  if(c instanceof OWLObjectOneOf)
	    return true;
	return false; 	
  }
     
  public ConceptLabel() 
  {
	this.concepts = new LinkedHashSet<OWLClassExpression>();
	 
  }
	
  public ConceptLabel(ConceptLabel cl) 
  {
	this.concepts = new LinkedHashSet<OWLClassExpression>(cl.getConcepts());
	this.dataRange = cl.getDataRange();//???
	hashcode = sumCode();
  }

  public ConceptLabel(Set<OWLClassExpression> s) 
  {
	this.concepts = new LinkedHashSet<OWLClassExpression>(s);
	//for(OWLClassExpression c : s)
		//if(c instanceof OWLObjectOneOf)
		//	this.concepts.add(((OWLObjectOneOf) c).asObjectUnionOf());
		//else
	//this.concepts.add(c);
	hashcode = sumCode();
  }
	 
  public ConceptLabel(OWLDataRange dr) 
  {
		this.concepts =  null;
		this.dataRange = dr;
  }	
	 
	public ConceptLabel(OWLClassExpression id) 
	{
		this.concepts = new LinkedHashSet<OWLClassExpression>( Collections.singleton(id) );
	    hashcode = sumCode(); 
	}
	
	public ConceptLabel(LinkedHashSet<OWLClassExpression> concepts, Set<OWLIndividual> inds) {
		this.concepts=concepts;
		this.individuals=inds;
		// TODO Auto-generated constructor stub
	}

	/*It changes this object!!!
	 *It is supposed that the object is not hashed in any structure
	 * 
	 */
	public void add(OWLClassExpression c) 
	{
		//if(c instanceof OWLObjectOneOf)
		//   if(c instanceof OWLObjectOneOf)
		//		this.concepts.add(((OWLObjectOneOf) c).asObjectUnionOf());
		//else
		this.concepts.add(c);
		hashcode = sumCode(); 
	}
	
	/*It changes this object!!!
	 *It is supposed that this object is not hashed in any structure
	 * 
	 */
	public void remove(OWLClassExpression c) 
	{
		this.concepts.remove(c);
		hashcode = sumCode();
	}
		 
	//It changes this object!!!
	//It is supposed that this object is not hashed in any structure
	public void addAll(Set<OWLClassExpression> ids) 
	{
	  for(OWLClassExpression c : ids)
			//if(c instanceof OWLObjectOneOf)
			//	this.concepts.add(((OWLObjectOneOf) c).asObjectUnionOf());
			//else
		this.concepts.add(c);
	  hashcode = sumCode();
	}
 
  public  ConceptLabel getNewConceptLabel(OWLClassExpression c) 
  {
	//if(c instanceof OWLObjectOneOf)
		//return new ConceptLabel(Sets.union(Collections.singleton(((OWLObjectOneOf) c).asObjectUnionOf()), new HashSet<OWLClassExpression>(this.concepts)));
	//	return new ConceptLabel(Sets.union(Collections.singleton(((OWLObjectOneOf) c).asObjectUnionOf()), new HashSet<OWLClassExpression>(this.concepts)));
	//else
	return new ConceptLabel(Sets.union(Collections.singleton(c), new HashSet<OWLClassExpression>(this.concepts)));
  }

	 
  public  ConceptLabel getNewConceptLabel(Set<OWLClassExpression> lc) 
  {
	Set<OWLClassExpression> ss = new HashSet<OWLClassExpression>(this.concepts);
	ss.addAll(lc);
	//for( OWLClassExpression c : lc)
			//if(c instanceof OWLObjectOneOf)
			//	ss.add(((OWLObjectOneOf) c).asObjectUnionOf());
			//else
	//  ss.add(c);
	return new ConceptLabel(ss);
  }

	public Set<OWLClassExpression> getAtomics()
	{
 		Set<OWLClassExpression> atos = new HashSet<OWLClassExpression> ();
		for(OWLClassExpression i : this.getConcepts()) {
		    if( !i.isAnonymous())
			atos.add(i);
		}
		return atos;
	}

	public Set<OWLClassExpression> getComplements()
	{
 		Set<OWLClassExpression> comp = new HashSet<OWLClassExpression> ();
		for(OWLClassExpression i : this.getConcepts()) {
		    if(i.getClassExpressionType() == ClassExpressionType.OBJECT_COMPLEMENT_OF)
			comp.add(i);
		}
		
		return comp;
	}

    public  boolean containsAll(ConceptLabel cl) {
		return this.concepts.containsAll(cl.getConcepts());
	}
	
	public  boolean contains(OWLClassExpression concept) {
		return this.concepts.contains(concept);
	}
	
	public  boolean containsIndividual(OWLNamedIndividual ind) 
	{
	    Set<OWLIndividual> inds = this.getIndividuals();
		return inds.contains(ind);
	}
	
	public void setConcepts(LinkedHashSet<OWLClassExpression> s) {
		this.concepts = s;
	}

	public LinkedHashSet<OWLClassExpression> getConcepts() {
		return this.concepts;
	}

	/*
	 * If it returns an empty set, it can contain an individual contained in a nominal concept as disjunction
	 */
	public Set<OWLIndividual> getIndividual()
	{

	  return this.individuals;
	}
	public Set<OWLIndividual> getIndividuals()
	{
	  Set<OWLIndividual> inds = new HashSet<OWLIndividual>();
	  for(OWLClassExpression c : this.concepts)
	  {
	      //a set of singleton disjunctions is a conjunction of nominals 
	    if(c instanceof OWLObjectOneOf && ((OWLObjectOneOf)c).getIndividuals().size()==1)
	    {
	      inds.addAll(((OWLObjectOneOf)c).getIndividuals());
	    }
	  }
	  return inds;
	}
	 
	public ConceptLabel removeNominals()
	{
	  ConceptLabel cl = new ConceptLabel(this);	
	  for(OWLClassExpression c : cl.getConcepts())
	  {
	     if(c instanceof OWLObjectOneOf)
		 {
		    cl.remove(c);
		 } 	
	  }
	  //cl.sumCode();
	  return cl;
	}
	
	
	public OWLDataRange getDataRange(){
	       return this.dataRange;
	}
	
	/*public void setNominals(Set<OWLObjectOneOf> nos)
	{
	       this.nominals = nos;
	}*/
	
	public void setDataRange(OWLDataRange dr)
	{
	       this.dataRange = dr;
	}
	/*
	 * Commutative of elements
	 */
    public int sumCode() 
    {
		long hash= 1234;	 
		for(OWLClassExpression c : this.concepts) 
		{	 
		  hash += c.hashCode();
		}
		return (int)(hash); 
    }
	@Override
    public int hashCode() 
	{	
	  return  hashcode; 
    }
	 
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null )
			return false;
		if (getClass() != obj.getClass())
			return false;
		ConceptLabel other = (ConceptLabel) obj;
		 
		if( !this.getConcepts().equals(other.getConcepts() )  ) {
		     //System.out.println("CL concepts EQUAL FALSE = "+ this.toString()+ "<>"+ other.toString());
		     return false;
		}
		 
		return true;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		ManchesterOWLSyntaxOWLObjectRendererImpl render = new ManchesterOWLSyntaxOWLObjectRendererImpl();
		//sb.append("Core : " + System.getProperty("line.separator"));
		if(concepts.size()==0) {
			  sb.append("Non-nominal star-type" + System.getProperty("line.separator") );
		}
		if(individuals!=null&&!individuals.isEmpty()) {
			sb.append("Individuals: ");
			for (OWLIndividual i :individuals ) {
			sb.append(render.render(i) +", ");
			}
		}
		if(concepts.size()==0) {
		  sb.append("EMPTY CORE" + System.getProperty("line.separator") );
		  return sb.toString();
		}  
		
		//int i =0;
	//	sb.append(": Hash="+hashcode+", ");
		sb.append("Concepts: ");
		for (OWLClassExpression co : concepts) {
			sb.append(render.render(co) +", ");
			//sb.append(System.getProperty("line.separator"));
		//	i++;
		}
		

		return sb.toString();
	}
	
	public String toSimpleString( ) 
	{
		ManchesterOWLSyntaxOWLObjectRendererImpl render = new ManchesterOWLSyntaxOWLObjectRendererImpl();
		String s = "";//"[Hash="+this.ID+", " ;
		for (OWLClassExpression co : concepts) {
			 
			s = s + render.render(co) + "," ;
			 
		}
		s=s+"]";
		return s;
	}
	public void toXML( PrintWriter writer ) {
		ManchesterOWLSyntaxOWLObjectRendererImpl render = new ManchesterOWLSyntaxOWLObjectRendererImpl();
		writer.print("[");
		for (OWLClassExpression co : concepts) {
			 
			writer.print(render.render(co) + "," );
			 
		}
		writer.print("]");
	}
	// currently not used
	public String toString(String oper) {
		StringBuilder sb = new StringBuilder();
		ManchesterOWLSyntaxOWLObjectRendererImpl render = new ManchesterOWLSyntaxOWLObjectRendererImpl();
		sb.append("Core, hashCode=" + hashcode + "," + System.getProperty("line.separator"));
		int i =0;
		if(concepts.isEmpty()) 
		   return "EMPTY\n";
		   
		for (OWLClassExpression co : concepts) {
		    if (oper.equals("literal")) {    
		        if(co.isClassExpressionLiteral() ){
			  sb.append("Concept "+i+" = "+ render.render(co) );
			  sb.append(System.getProperty("line.separator"));
			  i++;
			}
		    }else if(oper.equals("all")){
		        if(co.getClassExpressionType()== ClassExpressionType.OBJECT_ALL_VALUES_FROM ){
			  sb.append("Concept "+i+" = "+ render.render(co) );
			  sb.append(System.getProperty("line.separator"));
			  i++;
			}
		    }else if(oper.equals("some")){
		        if(co.getClassExpressionType()== ClassExpressionType.OBJECT_SOME_VALUES_FROM ){
			  sb.append("Concept "+i+" = "+ render.render(co) );
			  sb.append(System.getProperty("line.separator"));
			  i++;
			}
		    }else if(oper.equals("union")){
		        if(co.getClassExpressionType()== ClassExpressionType.OBJECT_UNION_OF ){
			  sb.append("Concept "+i+" = "+ render.render(co) );
			//  sb.append(System.getProperty("line.separator"));
			  i++;
			}
		    }else if(oper.equals("level1")){
		    
		            if(co.isClassExpressionLiteral() ){
			  	   sb.append("Concept "+i+" = "+ render.render(co) );
			           sb.append(System.getProperty("line.separator"));
			           i++;
			    
		            }else if(co.getClassExpressionType()== ClassExpressionType.OBJECT_ALL_VALUES_FROM &&
		              ((OWLObjectAllValuesFrom)co).getFiller().isClassExpressionLiteral()){
			       sb.append("Concept "+i+" = "+ render.render(co) );
			       sb.append(System.getProperty("line.separator"));
			       i++;
			       
		            }else if(co.getClassExpressionType()== ClassExpressionType.OBJECT_SOME_VALUES_FROM&&
		                ((OWLObjectSomeValuesFrom)co).getFiller().isClassExpressionLiteral()){
			          sb.append("Concept "+i+" = "+ render.render(co) );
			          sb.append(System.getProperty("line.separator"));
			          i++;
			    
		           }else if(co.getClassExpressionType()==ClassExpressionType.OBJECT_UNION_OF){
		               boolean noview = true;
		               for(OWLClassExpression c : ((OWLObjectUnionOf)co).getOperands()){
		                   if( !c.isClassExpressionLiteral() )
		                       noview = false;    
			       }
			       if( noview ){
			              sb.append("Concept "+i+" = "+ render.render(co) );
			              sb.append(System.getProperty("line.separator"));
			              i++;
			       }
		          }
		        
		    }
		    
		}//for

		return sb.toString();
	}



	public void setIndividual(Set<OWLIndividual> o) {
		// TODO Auto-generated method stub
		this.individuals=o;
		
	}

}
