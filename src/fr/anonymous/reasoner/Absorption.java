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
import java.util.HashSet;
import java.util.Set;

import org.semanticweb.owlapi.manchestersyntax.renderer.ManchesterOWLSyntaxOWLObjectRendererImpl;
import org.semanticweb.owlapi.model.ClassExpressionType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;

/*
  Concepts are manipulated as OWLExpressions in this class
  
*/
public class Absorption {
    int debug = 1;
    Set<ConceptAxiom> genConceptAxioms  ;
    Set<ConceptAxiom> equivAtomicAxioms  ;
    Set<ConceptAxiom> atomicAxioms  ;
    Set<ConceptAxiom> interAtomicAxioms  ;
	
    public Absorption(ReasoningData data) {	
	   genConceptAxioms = new HashSet<ConceptAxiom>();
	   equivAtomicAxioms =new HashSet<ConceptAxiom>(); 
	   atomicAxioms = new HashSet<ConceptAxiom>();
	   interAtomicAxioms = new HashSet<ConceptAxiom>();  
    }
   
	// A < C, A \equiv C, \exists R A < C , A \sqcap B < C 
	// This method updates : 
	// data.atomicAxioms, data.equivAtomicAxioms => data.atomicAxioms,  data.genConceptAxioms (equiv is privileged)
        // data.genConceptAxioms  => data.atomicAxioms,  data.someAtomicAxioms, data.genConceptAxioms
    public void absorbEquivAtomicInterAxioms(ReasoningData data) {
      	  Set<OWLClassExpression> atomics  = new HashSet<OWLClassExpression>();
      	  
	      Set<OWLClassExpression> equivAtomics  = new HashSet<OWLClassExpression>();
      	   
      	  Set<OWLClassExpression> interAtomics  = new HashSet<OWLClassExpression>();
	      OWLDataFactory factory = new OWLDataFactoryImpl();
	       
	      //"data.getAbsorbedSuperBySub is used for lazy applying rule  
      	      //EquivAtomicAxioms : A \equiv C. "equiv" has more priority than "atomic" and "neg atomic"
      	      //Each A in A = C is anonymous (already converted from \neg A < C in LoadingOntology)
 	      for(ConceptAxiom ax : equivAtomicAxioms ){
	  	  equivAtomics.add(ax.getLeftMember());
	  	  for(OWLClassExpression c : ax.getRightMember().asConjunctSet() )
	  	       data.getAbsorbedSupersBySub().put( new BinaryLabel(ax.getLeftMember()), c  );
	  	  OWLClassExpression comp = ax.getRightMember().getComplementNNF();
	  	   
	  	  for(OWLClassExpression c : comp.asConjunctSet() ){
	  	       data.getAbsorbedSupersBySub().put( new BinaryLabel(ax.getLeftMember().getComplementNNF()), c );
	  	   }
      	  }

	      //group atomicAxioms : A < C by A and remove A < C from  A < C if there is A = C  
	      // "atomic" has more priority than "neg atomic"
	      Set<ConceptAxiom> copyAtomicAxioms = new HashSet<ConceptAxiom>( atomicAxioms );
      	  for(ConceptAxiom ax : copyAtomicAxioms ){
	      //ignore \bot < C
	        if( !ax.getLeftMember().isOWLNothing() ) {
	           //group all A < C in if there is no A = C
	  	       if( !equivAtomics.contains(ax.getLeftMember()) ) {
	  	         atomics.add(ax.getLeftMember());
	  	         for(OWLClassExpression c : ax.getRightMember().asConjunctSet() )
	  	          data.getAbsorbedSupersBySub().put( new BinaryLabel(ax.getLeftMember()), c  );
	  	          
	  	       } else {
	  	          atomicAxioms.remove(ax);
	  	          genConceptAxioms.add(ax);
	  	       }
	         }
      	  }
      	  
      	   
      	   
      	  //interAxioms : A \sqcap B < C
      	  //Absorption A \sqcap B < C is better than A < \neg B \sqcup C
      	  Set<ConceptAxiom> copyInterAtomicAxioms = new HashSet<ConceptAxiom>( interAtomicAxioms );
      	  for(ConceptAxiom ax : copyInterAtomicAxioms ){
      	      
      	      Set<OWLClassExpression> leftConjuncts =  new HashSet<OWLClassExpression>( ax.getLeftMember().asConjunctSet() );
      	       
      	      //Can we reduce to one traverse of 
      	      Set<OWLClassExpression> abs = this.extractAbsorbableInter(ax.getLeftMember(), equivAtomics, interAtomics );
      	       
      	      if(abs.isEmpty()) {
      	         interAtomicAxioms.remove( ax );
	  	         genConceptAxioms.add( ax );
      	      } else {
      	         //convert  A \sqcap B < C to A < C \sqcup \neg B
      	         leftConjuncts.removeAll(abs); 
      	         Set<OWLClassExpression> terms =  new HashSet<OWLClassExpression>( ax.getRightMember().asDisjunctSet() );
      	        
      	         if( !leftConjuncts.isEmpty() ){
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
	  	    
      	          
      	         //OWLClassExpression notLeft =  left.getComplementNNF();
      	         //Set<OWLClassExpression> leftNNF = new HashSet<OWLClassExpression>( notLeft.asDisjunctSet() );
      	                    
      	         OWLClassExpression right  = null;
      	         if(terms.size() ==1) 
	  	            right = (OWLClassExpression)terms.toArray()[0]; 
	  	         else
	  	            right  = factory.getOWLObjectUnionOf(terms);
	  	 
	  	 
	  	         //OWLClassExpression nnf  = factory.getOWLObjectUnionOf(leftNNF);  
	  	         interAtomicAxioms.remove( ax );
	             Set<ConceptAxiom> binarizing = binarizingAbsorbableAxiom(new ConceptAxiom(left,  right), data);
	             interAtomicAxioms.addAll(binarizing);
	         
	             interAtomics.add(left);
      	         for(ConceptAxiom  axiom : binarizing) 
      	         {
      	           Set<OWLClassExpression> tr = new HashSet<OWLClassExpression>( axiom.getRightMember().asConjunctSet() );
      	           Object[] arr = axiom.getLeftMember().asConjunctSet().toArray();
      	           
      	           BinaryLabel bl = null;
      	           if(axiom.getLeftMember().asConjunctSet().size()==1)
      	             bl = new BinaryLabel( (OWLClassExpression)arr[0]);
      	           else 
      	           {
      	             bl = new BinaryLabel( (OWLClassExpression)arr[0], (OWLClassExpression)arr[1]);
      	           }  
	               for(OWLClassExpression c : tr )
	  	               data.getAbsorbedSupersBySub().put(bl, c );
	  	         }
      	      }	   
      	  }
                
	   
           
          //Reduction of general axioms : A < C , A < D => A <  C \sqcap D 
      	  Set<ConceptAxiom> genAxioms = new HashSet<ConceptAxiom>( genConceptAxioms );
          SetMultimap<OWLClassExpression, OWLClassExpression> finalGenAxioms = HashMultimap.create(); 
          for(ConceptAxiom ax : genAxioms){
	      finalGenAxioms.put(ax.getLeftMember(), ax.getRightMember()); 
	      genConceptAxioms.remove( ax );
          }
		  
      
          for(OWLClassExpression l : finalGenAxioms.keySet() ) 
          {
	        Set<OWLClassExpression>  rs =  finalGenAxioms.get(l);
	        OWLClassExpression[] rsArray = rs.toArray( new OWLClassExpression[rs.size()] );
	      
	        Set<OWLClassExpression> clsSet = new HashSet<OWLClassExpression>();
	        for(int i=0; i< rsArray.length; i++) 
	        {
	          clsSet.add( rsArray[i]  );
	        }
	          
	        OWLClassExpression rightCls = factory.getOWLObjectIntersectionOf(clsSet);
	      
	  	  
	        genConceptAxioms.add(new ConceptAxiom(l, rightCls)); 
          }
          
           
            
          if(debug==1) 
          { 
              File f = new File ("dumpAbsorption");
              PrintWriter writer = null;
	          try{ writer = new PrintWriter(new FileOutputStream(f));
	          }  catch(IOException e){}
	      
	          System.out.println("Ab: All axioms = " +  getAllAxioms().size() );
              writer.print( "Ab: All axioms = " +  getAllAxioms().size()+"\n\n");
              
	          System.out.println("Ab: General axioms = " +  genConceptAxioms.size() );
	          writer.print( "Ab: General axioms = " +  genConceptAxioms.size()+"\n\n");
	      
	          for(ConceptAxiom ax : genConceptAxioms){
       	          System.out.println("Ab : GEN LEFT = "+ (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(ax.getLeftMember()) );
       	          writer.print( "Ab : ========================================================= \n") ;
       	          writer.print( "Ab : LEFT GEN =" +   (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(ax.getLeftMember()) +"\n\n");
       	          System.out.println("Ab : RIGHT = "+ (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(ax.getRightMember()) );
       	          writer.print( "Ab : RIGHT GEN =  " +  (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(ax.getRightMember()) +"\n\n");
       	          
       	          
              }
       	      
       	      
	          System.out.println("Ab: Atomic axioms = " +  atomicAxioms.size() );
              writer.print( "Ab: Atomic axioms = " +  atomicAxioms.size()+"\n\n");
              
	      
       	      for(ConceptAxiom ax : atomicAxioms){
       	          System.out.println("Ab : ATOMIC LEFT = "+ (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(ax.getLeftMember()) );
       	          writer.print( "Ab : ========================================================= \n") ;
       	          writer.print( "Ab : ATOMIC LEFT  =" +   (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(ax.getLeftMember()) +"\n\n");
       	          System.out.println("Ab : ATOMIC RIGHT = "+ (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(ax.getRightMember()) +"\n\n");
       	          writer.print( "Ab : ATOMIC RIGHT  =  " +  (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(ax.getRightMember()) +"\n\n");
       	      }
       	      
       	      for(ConceptAxiom ax : equivAtomicAxioms){
       	          System.out.println("Ab : EQUIV LEFT = "+ (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(ax.getLeftMember()) );
       	          writer.print( "Ab : ========================================================= \n") ;
       	          writer.print( "Ab : EQUIV LEFT  =" +   (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(ax.getLeftMember()) +"\n\n");
       	          System.out.println("Ab : EQUIV RIGHT = "+ (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(ax.getRightMember()) +"\n\n");
       	          writer.print( "Ab : EQUIV RIGHT  =  " +  (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(ax.getRightMember()) +"\n\n");
       	      }
       	        
       	      
       	      System.out.println("Ab: Atomic Inter atomic axioms = " +  interAtomicAxioms.size() );
       	      writer.print( "Ab: Atomic Inter atomic axioms = " +  interAtomicAxioms.size()+"\n\n");
       	      for(ConceptAxiom ax : interAtomicAxioms){
       	          System.out.println("Ab : ATOMIC INTER  LEFT = "+ (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(ax.getLeftMember()) );
       	          writer.print( "Ab : ========================================================= \n") ;
       	          writer.print( "Ab : ATOMIC INTER LEFT =  " +  (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(ax.getLeftMember()) +"\n\n");
       	          System.out.println("Ab : ATOMIC INTER  RIGHT = "+ (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(ax.getRightMember()) +"\n\n");
       	          writer.print( "Ab : ATOMIC INTER  RIGHT =  " +  (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(ax.getRightMember()) +"\n\n");
       	      }
       	      
       	      
       	      System.out.println("Ab: AbsorbedSupersBySub = " +  data.getAbsorbedSupersBySub().size() );
       	      writer.print( "Ab: AbsorbedSupersBySub = " +  data.getAbsorbedSupersBySub().size()+"\n\n");
       	      for(BinaryLabel bl : data.getAbsorbedSupersBySub().keySet() ){
       	           System.out.println("Ab : Absorbed LEFT = "+ (new ConceptLabel(bl.getBoth())).toString()+"\n\n" );
       	           System.out.println("Ab : Absorbed RIGHT = "+ (new ConceptLabel(data.getAbsorbedSupersBySub().get(bl))).toString()+"\n\n" );
       	      }
       	      writer.close();
	      }

	}
	
	public Set<ConceptAxiom> binarizingAbsorbableAxiom(ConceptAxiom axiom, ReasoningData data) {
          OWLDataFactory factory = new OWLDataFactoryImpl();
          OWLClassExpression subClass   = axiom.getLeftMember();
                //System.out.println( "LOAD : binarizing, subClass=" +   (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(subClass) +"\n\n");
          OWLClassExpression superClass = axiom.getRightMember();
          if( subClass.asConjunctSet().size() <= 2 ) {
              Set<ConceptAxiom> res = new HashSet<ConceptAxiom>();
		      res.add ( axiom );
		     return res;
          }
                     
          Set<OWLClassExpression> copyConjuncts =  new HashSet<OWLClassExpression>(subClass.asConjunctSet());
          OWLClassExpression conj1 = (OWLClassExpression)copyConjuncts.toArray()[0];
          copyConjuncts.remove(conj1);
          OWLClassExpression conj2 = (OWLClassExpression)copyConjuncts.toArray()[0]; 
          copyConjuncts.remove(conj2);
                
          OWLClass F1 = factory.getOWLClass(IRI.create("http://linc/owl#conceptNameByAbsorption_Binary_"+ data.getNewConceptID()) );
          // TODO check if it is the initial atomic concepts here, and not the derived ones
          data.getInitialAtomicConcepts().add(F1);
                //OWLClassExpression remaining = factory.getOWLObjectIntersectionOf( copyConjuncts );
          Set<ConceptAxiom> res = new HashSet<ConceptAxiom>();
                     
          Set<OWLClassExpression> clsSet1 = new HashSet<OWLClassExpression>();
          clsSet1.add( conj1 );
		  clsSet1.add( conj2 );
		  OWLClassExpression newLeft1 = factory.getOWLObjectIntersectionOf( clsSet1 );
		      
		  res.add( new ConceptAxiom( newLeft1, F1) );
		     
		  clsSet1.clear();
		  clsSet1.add( F1 );
		  clsSet1.addAll( copyConjuncts  );
		  newLeft1 = factory.getOWLObjectIntersectionOf( clsSet1 );
		
		  // Recursion     
		  res.addAll( binarizingAbsorbableAxiom(new ConceptAxiom(newLeft1, superClass), data) );
		      
	      return res; 
    }
          
	public Set<OWLClassExpression> extractAbsorbableInter(OWLClassExpression c, Set<OWLClassExpression> equivAtomics, Set<OWLClassExpression> inters  ) {
	    Set<OWLClassExpression> abs = new HashSet<OWLClassExpression>();                             
	    if(c.getClassExpressionType()!=ClassExpressionType.OBJECT_INTERSECTION_OF) {
	           return abs;
	    }
	    
        for(OWLClassExpression i : c.asConjunctSet()) {
                    
             	    if( !i.isAnonymous()   && !equivAtomics.contains(i)  ) {
 
             	           abs.add(i);            	         
             	    }  
        } 
        return abs;   
    }
            
	public boolean isOperandOfComplements(OWLClassExpression c, Set<OWLClassExpression> negs ) {
	       for(OWLClassExpression i :  negs) {
	           OWLClassExpression opera = ((OWLObjectComplementOf)i).getOperand();
	           if(c.equals(i))
	              return true;
	       }
	       return false;
	}
	
	public Set<ConceptAxiom> getGenConceptAxioms() {
		return genConceptAxioms;
	}

	public void setGenConceptAxioms(Set<ConceptAxiom> s) {
	       genConceptAxioms = s;
	}

	 
	public Set<ConceptAxiom> getEquivAtomicAxioms() {
		return equivAtomicAxioms;
	}

	public void setEquivAtomicAxioms(Set<ConceptAxiom> s) {
	       equivAtomicAxioms = s;
	}

	 
	public Set<ConceptAxiom> getAtomicAxioms() {
		return atomicAxioms;
	}

	public void setAtomicAxioms(Set<ConceptAxiom> s) {
	       atomicAxioms = s;
	}
	
	public void setInterAtomicAxioms(Set<ConceptAxiom> s) {
	       interAtomicAxioms = s;
	}
	
	public Set<ConceptAxiom> getInterAtomicAxioms( ) {
	       return interAtomicAxioms;
	}
	
	public Set<ConceptAxiom> getAllAxioms() { 
	    Set<ConceptAxiom> allAxioms = new HashSet<ConceptAxiom>( this.genConceptAxioms );
	    //allAxioms.addAll( this.equivConceptAxioms );
	    allAxioms.addAll( this.equivAtomicAxioms );
	    //allAxioms.addAll( this.equivNegAtomicAxioms );
	    allAxioms.addAll( this.atomicAxioms ); 
	    
	    allAxioms.addAll( this.interAtomicAxioms );
	    //allAxioms.addAll( this.equivSomeAtomicAxioms );
	    //allAxioms.addAll( this.allAtomicAxioms );
	    //allAxioms.addAll( this.equivAllAtomicAxioms );
	    return allAxioms; 
	}
	
        
}
