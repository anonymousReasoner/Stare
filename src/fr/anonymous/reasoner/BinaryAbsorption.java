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

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.Vector;
/*
 *  Concepts are manipulated as OWLExpressions in this class
 *  It can absorb negated or no negated atomic concepts.
 *  If both A and \neg A are there (A and \neg are not absorbable directly), we can add (A \sqcup \neg A) to nodes 
 *     which contain neither A nor \neg A. This allows to exploit the fact that many nodes contain either A or \neg A
 */
import org.semanticweb.owlapi.model.ClassExpressionType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;
import com.google.common.collect.Sets;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;
import uk.ac.manchester.cs.owl.owlapi.mansyntaxrenderer.ManchesterOWLSyntaxOWLObjectRendererImpl;

import static org.semanticweb.owlapi.vocab.OWLDataFactoryVocabulary.OWLThing;

public class BinaryAbsorption 
{
    int debug = 0;
    int debugPrint = 0;
    Set<ConceptAxiom> genConceptAxioms;
    Set<ConceptAxiom> atomicAxioms;  // It includes binary on the left side, and negated concepts
   
    public BinaryAbsorption() 
    {	
	   genConceptAxioms = new HashSet<>(); // filled by LoadingOntology
	   atomicAxioms = new HashSet<>();   // filled by LoadingOntology (absorbable axioms : binary, negated concepts)
    }
    
    //This method absorbs binary axioms and stores in ReasoningData
    //It creates AbsorbedAtomic and AbsorbedNegated in rData
    public void absorbBinaryAxioms(ReasoningData rData)
    {
	   OWLDataFactory factory = new OWLDataFactoryImpl();
       for(ConceptAxiom ax : atomicAxioms ) {  //the left member is binary
       	  Object[] left = ax.getLeftMember().asConjunctSet().toArray();
	      if(ax.getLeftMember().asConjunctSet().size()==1)
	      {
	         OWLClassExpression one = (OWLClassExpression)left[0]; 
	         if( !one.isOWLNothing() ) //ignore \bot < C
	         {
	        	if( one.isClassExpressionLiteral() ) {//atomic or negated
	        	   if( !one.isAnonymous() )
	        		 rData.getAbsorbedAtomic().add(one);
	        	   else {
	        		 OWLClassExpression neg = ((OWLObjectComplementOf)one).getOperand(); 
	        		 rData.getAbsorbedNegated().add(neg);

	        	   	}
	        	   for(OWLClassExpression c : ax.getRightMember().asConjunctSet() )
		  	       {
		  	         rData.getAbsorbedSupersBySub().put(new BinaryLabel(one), c );
		  	       }
	            } else { //some
	  	           for(OWLClassExpression c : ax.getRightMember().asConjunctSet() )
	  	           {
	  	             rData.getAbsorbedSupersBySub().put(new BinaryLabel(one), c );
	  	           }
	            }
	         }//
	      } else {
	         OWLClassExpression c1 = (OWLClassExpression)left[0];
	         OWLClassExpression c2 = (OWLClassExpression)left[1];   
	         if( !c1.isOWLNothing() && !c2.isOWLNothing() ) {// tautology otherwise,
	        	if( c1.isClassExpressionLiteral() ) {//atomic or negated
	        	 if( !c1.isAnonymous() )
	        		 rData.getAbsorbedAtomic().add(c1);
	        	 else {
	        		 OWLClassExpression neg = ((OWLObjectComplementOf)c1).getOperand(); 
	        		 rData.getAbsorbedNegated().add(neg);
	        	 }
	        	}
	        	if( c2.isClassExpressionLiteral() ) {//atomic or negated
	        	 if( !c2.isAnonymous() )
	        		 rData.getAbsorbedAtomic().add(c2);
	        	 else {
	        		 OWLClassExpression neg = ((OWLObjectComplementOf)c2).getOperand(); 
	        		 rData.getAbsorbedNegated().add(neg);
	        	 }
	        	}
	        	
	            BinaryLabel bl = new BinaryLabel(c1, c2);
	  	        for(OWLClassExpression c : ax.getRightMember().asConjunctSet()) {
	  	             rData.getAbsorbedSupersBySub().put(bl, c );
	  	        }
	         }
	      }
       }
       //It seems we can absorb until X with (... and ... some and  ...X) e.g OBI
       //Each equivAtomic axiom may be moved to atomic or general.  
       //Let A = X. If A is contained in AbsorbedAtomic or AbsorbedNegated, A=X is moved to GeneralAxioms  
       //Note : A = X_1, A = X_2 implies X_1=X_2  
       /*for(ConceptAxiom ax : equivAtomicAxioms ) // A or -A on the left side
       {
    	   OWLClassExpression left = ax.getLeftMember();
    	   if( left.isClassExpressionLiteral() && !left.isAnonymous() )
	       {
    		   if(  rData.getAbsorbedNegated().contains(left) )
    		       genConceptAxioms.add( ax );
    		   else 
    		   {
    			   rData.getAbsorbedAtomic().add(left);
	        	   for(OWLClassExpression c : ax.getRightMember().asConjunctSet() )
		  	       {
		  	         rData.getAbsorbedSupersBySub().put(new BinaryLabel(left), c);
		  	       }
    		   }
	       } else if( left.isClassExpressionLiteral() && left.isAnonymous() )
	       {
	    	   OWLClassExpression op = ((OWLObjectComplementOf)left).getOperand();
	    	   if( rData.getAbsorbedAtomic().contains(op) )
	    		   genConceptAxioms.add( ax );
	    	   else 	   
	           {
	        	   OWLClassExpression neg = ((OWLObjectComplementOf)left).getOperand(); 
	        	   rData.getAbsorbedNegated().add(neg);
	        	   for(OWLClassExpression c : ax.getRightMember().asConjunctSet() )
		  	       {
		  	         rData.getAbsorbedSupersBySub().put(new BinaryLabel(left), c );
		  	          
		  	       }
	           } 	   
	       } else
	       {
	    	   genConceptAxioms.add( ax );
	       }
       }*/ 
       
       //Reduction of general axioms : A < C , A < D => A <  C \sqcap D 
       Set<ConceptAxiom> genAxioms = new HashSet<>( genConceptAxioms );
       SetMultimap<OWLClassExpression, OWLClassExpression> finalGenAxioms = HashMultimap.create(); 
       for(ConceptAxiom ax : genAxioms)
       {
	          finalGenAxioms.put(ax.getLeftMember(), ax.getRightMember()); //regroup axioms which have the same left side
	          genConceptAxioms.remove( ax );
       }  
      
       for(OWLClassExpression l : finalGenAxioms.keySet() ) // A <= C1, A<= C2 ==> A <= C1 /\ C2  
       {
	          Set<OWLClassExpression>  rs =  finalGenAxioms.get(l);
	          if ( rs.isEmpty() )
	          	  continue;
	          genConceptAxioms.add(new ConceptAxiom(l, factory.getOWLObjectIntersectionOf(rs)));
       }
       
       if(debug==1) 
       {
          File f = new File ("dumpAbsorption");
          PrintWriter writer = null;
	      try{ 
	    	  writer = new PrintWriter(new FileOutputStream(f));
	      }  catch(IOException e){

		  }
	      
	      System.out.println("Ab: All axioms = " +  getAllAxioms().size() );
          writer.print( "Ab: All axioms = " +  getAllAxioms().size()+"\n\n");
              
	      System.out.println("Ab: General axioms = " +  genConceptAxioms.size() );
	      writer.print( "Ab: General axioms = " +  genConceptAxioms.size()+"\n\n");
	      
	      if(debugPrint==1) {
	      for(ConceptAxiom ax : genConceptAxioms)
	      {
       	          System.out.println("Ab : GEN LEFT = "+ (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(ax.getLeftMember()) );
       	          writer.print( "Ab : ========================================================= \n") ;
       	          writer.print( "Ab : LEFT GEN =" +   (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(ax.getLeftMember()) +"\n\n");
       	          System.out.println("Ab : RIGHT = "+ (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(ax.getRightMember()) +"\n\n");
       	          writer.print( "Ab : RIGHT GEN =  " +  (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(ax.getRightMember()) +"\n\n");
       	  }
	      
	      System.out.println("Press enter!");
	      }
	      
	      System.out.println("Ab: Atomic axioms = " +  atomicAxioms.size() );
          writer.print( "Ab: Atomic axioms = " +  atomicAxioms.size()+"\n\n");
          if(debugPrint==1) {
       	  for(ConceptAxiom ax : atomicAxioms)
       	  {
       	          System.out.println("Ab : ATOMIC LEFT = "+ (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(ax.getLeftMember()) );
       	          writer.print( "Ab : ========================================================= \n") ;
       	          writer.print( "Ab : ATOMIC LEFT  =" +   (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(ax.getLeftMember()) +"\n\n");
       	          System.out.println("Ab : ATOMIC RIGHT = "+ (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(ax.getRightMember()) +"\n\n");
       	          writer.print( "Ab : ATOMIC RIGHT  =  " +  (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(ax.getRightMember()) +"\n\n");
       	  }
          }
          
       	  System.out.println("Ab: AbsorbedSupersBySub = " +  rData.getAbsorbedSupersBySub().size() );
       	  writer.print( "Ab: AbsorbedSupersBySub = " +  rData.getAbsorbedSupersBySub().size()+"\n\n");
       	  
       	  if(debugPrint==1) {
       	  for(BinaryLabel bl : rData.getAbsorbedSupersBySub().keySet() )
       	  {
       	           System.out.println("Ab : Absorbed LEFT = "+ (new ConceptLabel(bl.getBoth())).toString()+"\n\n" );
       	           System.out.println("Ab : Absorbed RIGHT = "+ (new ConceptLabel(rData.getAbsorbedSupersBySub().get(bl))).toString()+"\n\n" );
       	  }
       	  
       	  for(OWLClassExpression c : Sets.intersection(rData.getAbsorbedAtomic(), rData.getAbsorbedNegated()))
     	  {
       		System.out.println("Absorbed atomic and negated = "+ (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(c) );
     	  }
       	  }
       	  
       	  System.out.println("Absorbed atomic and negated NB = " +Sets.intersection(rData.getAbsorbedAtomic(), rData.getAbsorbedNegated()).size());
       	  writer.close();
       	  
       	  System.out.println("Press enter!");
          
	  }
	}
    
    
    public Set<ConceptAxiom> absorbPart(ConceptAxiom ax, ReasoningData data)
    {
    	OWLDataFactory factory = new OWLDataFactoryImpl();  
    	Set<OWLClassExpression> leftConjuncts =  new HashSet<>( ax.getLeftMember().asConjunctSet() );
	      //Can we reduce to one traverse of 
	    Set<OWLClassExpression> abs = this.extractAbsorbableInter( ax.getLeftMember() );
	    Set<ConceptAxiom> res = new HashSet<>();
	    if(abs.isEmpty()) 
	    {
	    	 res.add(ax);
	         return res;
	    } else 
	    {
	         //convert  A_1 /\ ... /\ A_n /\ B < C to A_1 /\ ... /\ A_n < C \sqcup \neg B
	         leftConjuncts.removeAll(abs); 
	         Set<OWLClassExpression> terms =  new HashSet<>( ax.getRightMember().asDisjunctSet() );
	         if( !leftConjuncts.isEmpty() )
	         {
	            OWLClassExpression tmp  = factory.getOWLObjectIntersectionOf( leftConjuncts );
	            tmp = tmp.getComplementNNF();
	            terms.addAll(tmp.asDisjunctSet());
	            
	            if(terms.size() > 1)
	               terms.remove( factory.getOWLNothing() );
	         }
	         
	         OWLClassExpression left  = null;
	         if(abs.size() ==1) 
	            left = (OWLClassExpression)abs.toArray()[0]; 
	         else
	            left  = factory.getOWLObjectIntersectionOf(abs);                   
	         OWLClassExpression right  = null;
	         if(terms.size() ==1) 
	            right = (OWLClassExpression)terms.toArray()[0]; 
	         else
	            right  = factory.getOWLObjectUnionOf(terms);
	         //When an axiom changes, we run again "binarizing..." on that changed axiom.
	         res.addAll( absorbAxiom(new ConceptAxiom(left,  right), data) );
	          
             return res;
	    }
    }
        
   
    //This method returns a new axiom whose subsume is the largest absorbable part of "c"
  	//It returns null if otherwise
//  	public boolean isAbsorbableInter( OWLClassExpression c )
//  	{
//  	    if( c.getClassExpressionType()!=ClassExpressionType.OBJECT_INTERSECTION_OF)
//  	           return false;
//  	    // return true if it contains at least one atomic or some
//        for( OWLClassExpression i : c.asConjunctSet() ) {
//              if( !i.isAnonymous() || this.containsOnlyInterSome(i) )
//               	return true;
//        }
//        return false;
//    }
  	
  	public boolean isAbsorbableInterLiteral( OWLClassExpression c ) 
  	{
//  	    if( c.getClassExpressionType() != ClassExpressionType.OBJECT_INTERSECTION_OF)
//  	        return false;
  	    // return true if it contains at least one atomic or some    
        for( OWLClassExpression i : c.asConjunctSet() ) {
             if( i.isClassExpressionLiteral() || this.containsOnlyInterSomeLiteral(i) ) 
               	 return true;   
        }
        return false;
    } 
          
    // A concept contains only conjunctions, existential restrictions and atomics 
    public boolean containsOnlyInterSome( OWLClassExpression c ) 
    {
  	       if( !c.isAnonymous() )
  	            return true;
//  	       if( c.getClassExpressionType()==ClassExpressionType.OBJECT_INTERSECTION_OF )
//  	       {
//  	           for(OWLClassExpression conc : c.asConjunctSet())
//  	           {
//  	        	   if( !containsOnlyInterSome(conc) )
//  	        		   return false;
//  	           }
//  	           return true;
//  	       }
  	       else if(c.getClassExpressionType()==ClassExpressionType.OBJECT_SOME_VALUES_FROM )
  	       {
  	                 OWLClassExpression filler = ((OWLObjectSomeValuesFrom)c).getFiller();
  	                 if( !filler.isAnonymous() )
  			             return true;
  			         else
  			             return containsOnlyInterSome(filler);     	 
           } else
              return false;
    }
    
    public boolean containsOnlyInterSomeLiteral( OWLClassExpression c ) 
    {
  	       if( c.isClassExpressionLiteral() )
  	            return true;
//  	       if( c.getClassExpressionType()==ClassExpressionType.OBJECT_INTERSECTION_OF )
//  	       {
//  	           for(OWLClassExpression conc : c.asConjunctSet())
//  	           {
//  	        	   if( !containsOnlyInterSomeLiteral(conc) )
//  	        		   return false;
//
//  	           }
//  	           return true;
//  	       }
//
		   else if(c.getClassExpressionType()==ClassExpressionType.OBJECT_SOME_VALUES_FROM )
  	       {
  	               OWLClassExpression filler = ((OWLObjectSomeValuesFrom)c).getFiller();
  	               if( filler.isClassExpressionLiteral() )
  			           return true;
  			       else
  			           return containsOnlyInterSomeLiteral(filler);     	 
           }
  	       else
           	return false;
   		 }
          
          // It is supposed that "exp" is "containsOnlyInterSome"
          // adds fresh concepts names 
    public Set<ConceptAxiom> absorbAxiom(ConceptAxiom axiom, ReasoningData data)
    {
        OWLClassExpression subClass   = axiom.getLeftMember();
        OWLClassExpression superClass = axiom.getRightMember();
        if( !subClass.isAnonymous() )
        {
        	Set<ConceptAxiom> res = new HashSet<>();
            res.add( axiom );
            return res;
        } 
        else if(subClass.getClassExpressionType()==ClassExpressionType.OBJECT_SOME_VALUES_FROM)
        {
              Vector<OWLClassExpression> newF = new Vector<>();
              Set<ConceptAxiom> res = new HashSet<>();
              res.addAll( absorbLeftSome(subClass, superClass, newF, data) );
              return res;
        }
        else if(subClass.getClassExpressionType()==ClassExpressionType.OBJECT_INTERSECTION_OF)
        {
              Set<ConceptAxiom> binaryAxioms = binarizingAbsorbableAxiom(axiom, data);
              Set<ConceptAxiom> res = new HashSet<>();

              for(ConceptAxiom ax : binaryAxioms)
              {
                  res.addAll ( absorbBinaryAxiom( ax, data ) );
              }
              return res;
          }
        else {
              Set<ConceptAxiom> res = new HashSet<>();
              res.add(axiom);
              return res;
          }
    }
    
    //This methods convert \exists R A => (A <= \forall R^- F)
    public ConceptAxiom absorbSome( OWLClassExpression someClass,
    		                 Vector<OWLClassExpression> newF, ReasoningData data )
    {
  	   // OWLDataFactory factory = new OWLDataFactoryImpl();
  	  //  OWLClassExpression filler = ((OWLObjectSomeValuesFrom)someClass).getFiller(); //it may be negated
  	   // OWLObjectPropertyExpression prop = ((OWLObjectSomeValuesFrom)someClass).getProperty();
  	    //OWLClass F1 = factory.getOWLClass(IRI.create("http://linc/owl#conceptNameByAbsorption_Some_"+ data.getNewConceptID()) );
  	   // data.getDerivedAtomicConcepts().add( someClass);
  	   newF.add(someClass);
  	   // OWLObjectPropertyExpression inv = prop.getInverseProperty().getSimplified();
  	   // OWLClassExpression right = factory.getOWLObjectAllValuesFrom( inv, F1 );
		//data.getDerivedAtomicConcepts().add((OWLClass) someClass);

		//data.getDerivedAtomicConcepts().add( someClass);
  	    return new ConceptAxiom( someClass, OWLThing);
	}
                          
    // "someClass" is \exists R X with X absorbable (atomic or negated)
    // Return X < \forall R-.F where F is fresh
    // "newF" contains F 
    // This method is called if (Y and \exists R X) < C where Y and X are absorbable (atomic or negated)
    // there was a bug: we have to add also F <= C
    public Set<ConceptAxiom> absorbLeftSome(OWLClassExpression someClass, OWLClassExpression superClass, 
    		Vector<OWLClassExpression> newF, ReasoningData data )
    {
    	  OWLDataFactory factory = new OWLDataFactoryImpl();
    	  OWLClassExpression filler = ((OWLObjectSomeValuesFrom)someClass).getFiller();//it may be negated
    	  OWLObjectPropertyExpression prop = ((OWLObjectSomeValuesFrom)someClass).getProperty();
//    	  OWLClass F1 = factory.getOWLClass(IRI.create("http://linc/owl#conceptNameByAbsorption_Some_"+ data.getNewConceptID()) );
//    	  data.getDerivedAtomicConcepts().add(F1);
//    	  newF.add(F1);
//    	  OWLObjectPropertyExpression inv = prop.getInverseProperty().getSimplified();
//    	  OWLClassExpression right = factory.getOWLObjectAllValuesFrom( inv, F1 );
          Set<ConceptAxiom> result = new HashSet<>();
//    	  if( filler.isOWLThing() )
//
    		  data.getRightConjunctsOfTop().add(someClass);
    	  result.add(new ConceptAxiom( someClass, superClass));
    	//  result.add(new ConceptAxiom( filler, right));
    	 // result.add(new ConceptAxiom( F1, superClass));
    	  return result;
    }
          
    //It is supposed that  "someClass" has 1 level
    public Set<ConceptAxiom> absorbAtomicAndSome(OWLClassExpression ato,  OWLClassExpression superClass,OWLClassExpression someClass,
												 Vector<OWLClassExpression> newF, ReasoningData data)
    {
		//System.out.println("yes");
    	OWLDataFactory factory = new OWLDataFactoryImpl();
     
    	ConceptAxiom axSome = absorbSome(someClass, newF, data);
    	Set<OWLClassExpression> clsSet1 = new HashSet<>();
  	    clsSet1.add( newF.get(0) );
  	    clsSet1.add( ato );
  	    OWLClassExpression newLeft = factory.getOWLObjectIntersectionOf( clsSet1 );
  	    Set<ConceptAxiom> result = new HashSet<>();
  	    //result.add(someClass);
  	    result.add(new ConceptAxiom(ato, superClass) );

    	return  result;
    }
    
  //It is supposed that  "someClass" has 1 level
    public Set<ConceptAxiom> absorbTwoSomes(OWLClassExpression some1, OWLClassExpression some2, OWLClassExpression superClass,
    	                     ReasoningData data)
    {
    	Vector<OWLClassExpression> newF = new Vector<>();
    	ConceptAxiom axS = absorbSome(some2, newF, data);
    	OWLClassExpression new1 = newF.get(0);
    	newF.clear();
    	Set<ConceptAxiom> ss = absorbAtomicAndSome(new1, some1, superClass, newF, data);
    	Set<ConceptAxiom> result = new HashSet<>();
    	result.add ( axS );
    	result.addAll( ss );
    	return  result;
    }
    
    /*      
     * "subClass" is a conjunction of 2 absorbable conjuncts ; axiom subClass < superClass 
     * Considers the cases :  A_1 and A_2 < C with A_i atomic; A_1 and \exists R.X ; \exists R_1. X_1 and \exists R_2.X_2 ;  
     *     ; \neg A_1 and A_2; \neg A_1 and \exists R. A_2; \neg A_1 and \neg A_2; (30/12/2017)   
     */    
    public Set<ConceptAxiom> absorbBinaryAxiom(ConceptAxiom axiom, ReasoningData data)
    {
//    	HashSet<ConceptAxiom> h = new HashSet<>();
//    	h.add(axiom);
//    	return h;
    	OWLClassExpression subClass   = axiom.getLeftMember();
    	OWLClassExpression superClass = axiom.getRightMember();

    	Object[] arr = subClass.asConjunctSet().toArray();

    	OWLClassExpression conj1 = (OWLClassExpression)arr[0];
    	OWLClassExpression conj2 = (OWLClassExpression)arr[1];
        if( conj1.isClassExpressionLiteral() &&  conj2.isClassExpressionLiteral() )
    	{
    		return new HashSet<>( Collections.singleton(axiom) );
    	}

    	if( conj1.getClassExpressionType()==ClassExpressionType.OBJECT_SOME_VALUES_FROM &&
    		conj2.getClassExpressionType()==ClassExpressionType.OBJECT_SOME_VALUES_FROM )
    	{
			return absorbTwoSomes(conj1, conj2, superClass,  data);
    	}

    	OWLClassExpression someClass=null;
    	OWLClassExpression atoClass=null; // ClassExpressionLiteral
    	if(  conj1.getClassExpressionType()==ClassExpressionType.OBJECT_SOME_VALUES_FROM)
    		someClass = conj1;
    	else
    		atoClass= conj2;

    	if( conj2.getClassExpressionType()==ClassExpressionType.OBJECT_SOME_VALUES_FROM)
    		someClass = conj2;
    	else
    		atoClass= conj1;

    	Vector<OWLClassExpression> newF = new Vector<>();
    	return absorbAtomicAndSome(atoClass, someClass, superClass,newF,  data);

    }
          
      //"subClass" is a conjunction of N conjuncts with N > 1 : 
      // C_1 /\ ... /\ C_n /\ \exists R_1. B_1 /\ ... \exists R_1. B_1 <= C 
      // Return a set of binary axioms of the form X_1 and X_2 < C
    public Set<ConceptAxiom> binarizingAbsorbableAxiom(ConceptAxiom axiom, ReasoningData data) {
    	OWLDataFactory factory = new OWLDataFactoryImpl();
    	OWLClassExpression subClass   = axiom.getLeftMember();
    	OWLClassExpression superClass = axiom.getRightMember();
    	if( subClass.asConjunctSet().size() <= 2 ) {
    		Set<ConceptAxiom> res = new HashSet<>();
    		res.add ( axiom );
    		return res;
    	}
    	Set<OWLClassExpression> copyConjuncts =  new HashSet<>(subClass.asConjunctSet());
    	OWLClassExpression conj1 = (OWLClassExpression)copyConjuncts.toArray()[0];
    	copyConjuncts.remove(conj1);
    	OWLClassExpression conj2 = (OWLClassExpression)copyConjuncts.toArray()[0];
    	copyConjuncts.remove(conj2);

    	OWLClass F1 = factory.getOWLClass(IRI.create("http://linc/owl#conceptNameByAbsorption_Binary_"+ data.getNewConceptID()) );
    	data.getDerivedAtomicConcepts().add(F1);

    	Set<ConceptAxiom> res = new HashSet<>();

    	Set<OWLClassExpression> clsSet1 = new HashSet<>();
    	clsSet1.add( conj1 );
    	clsSet1.add( conj2 );

    	OWLClassExpression newLeft1 = factory.getOWLObjectIntersectionOf( clsSet1 );
    	//C_i and C_j <= A
    	res.add( new ConceptAxiom( newLeft1, F1) );


    	clsSet1.clear();
    	clsSet1.add( F1 );
    	clsSet1.addAll( copyConjuncts  );
    	// A and (remainder of subClass)
    	newLeft1 = factory.getOWLObjectIntersectionOf( clsSet1 );

    	// Recursion
    	res.addAll( binarizingAbsorbableAxiom(new ConceptAxiom(newLeft1, superClass), data) );

    	return res;
    }
	
	// Compute all atomics or negated concepts occuring in "c" (left hand side of an axiom) which are absorbable  
	public Set<OWLClassExpression> extractAbsorbableInter(OWLClassExpression c  ) 
	{
	    Set<OWLClassExpression> abs = new HashSet<>();
//	    if(c.getClassExpressionType()!=ClassExpressionType.OBJECT_INTERSECTION_OF)
//	    {
//	           return abs;
//	    }
        for(OWLClassExpression i : c.asConjunctSet()) 
        {
        	if( i.isClassExpressionLiteral() || containsOnlyInterSomeLiteral(i) )
        	    abs.add(i);
        } 
        return abs;   
    }
	
	public Set<ConceptAxiom> getGenConceptAxioms() {
		return genConceptAxioms;
	}
	
	Vector<OWLClassExpression> newF = new Vector<>();
	public void setGenConceptAxioms(Set<ConceptAxiom> s) 
	{
	       genConceptAxioms = s;
	}

	public Set<ConceptAxiom> getAtomicAxioms() 
	{
		return atomicAxioms;
	}

	
	public void setAtomicAxioms(Set<ConceptAxiom> s) {
	       atomicAxioms = s;
	}

	
	public Set<ConceptAxiom> getAllAxioms() { 
	    Set<ConceptAxiom> allAxioms = new HashSet<>( this.genConceptAxioms );
	    
	    allAxioms.addAll( this.atomicAxioms ); 
	    
	  
	    return allAxioms; 
	}
}
