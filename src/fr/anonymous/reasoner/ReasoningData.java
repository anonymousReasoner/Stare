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
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import org.semanticweb.owlapi.model.ClassExpressionType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDataMinCardinality;
import org.semanticweb.owlapi.model.OWLDataPropertyExpression;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectInverseOf;
import org.semanticweb.owlapi.model.OWLObjectMinCardinality;
import org.semanticweb.owlapi.model.OWLObjectOneOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLPropertyExpression;
import org.semanticweb.owlapi.model.OWLQuantifiedRestriction;
import org.semanticweb.owlapi.model.PrefixManager;

import com.google.common.base.Optional;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;
import com.google.common.collect.Sets;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;

/*
 * This class stores all data for reasoning including an initial ABox, derived named individuals, named concepts
 *
 */

public class ReasoningData implements Serializable
{
	private static final long serialVersionUID = 1L;
	private Optional<IRI>  IRIBase;
	private boolean containsNominal = false;
	private boolean containsUnion = false;
	private boolean containsSome = false;
	private boolean containsCardinality = false;
	private boolean containsHierarchy = false;
	private boolean containsTransitive = false;
	private boolean containsInverse = false;
	private boolean containsDatatype = false;
	private boolean containsLk=false;
	private static OWLDataFactory factory = new OWLDataFactoryImpl();
	private SetMultimap<OWLPropertyExpression,  OWLPropertyExpression> superClosureByRole;
	private SetMultimap<OWLPropertyExpression, OWLPropertyExpression> subClosureByRole;
	private Set<OWLClass> initialAtomicConcepts;
	private Set<OWLClass> derivedAtomicConcepts;
	//these three structures are also defined in OntologyData
	private SetMultimap<BinaryLabel, OWLClassExpression> absorbedSupersBySub;
	private Set<OWLClassExpression> absorbedAtomic;
	private Set<OWLClassExpression> absorbedNegated;
	private Map<OWLDataPropertyExpression, RoleAttributes> dataPropWithAttr; //planed for transitive closure of roles
	private Map<OWLObjectPropertyExpression, RoleAttributes> objectPropWithAttr;
	// initAbox contains all information on individuals, initial or derived assertions from ontology
	// a current ABox contains a pointer to initABox
	private ABox initABox;
	// LK box
	private LKBox LK;
	// names for  MIN
	private Map<OWLClassExpression, List<OWLClass>> minNames;
	private int individualID = 0;
	private int conceptID = 0;
	private OWLClass top=null;
	private OWLClass bottom=null;
	private ConceptLabel emptyCore = null;
	private ConceptLabel initCore=null;
	private OWLIndividual dummyInd = null; //It is set if there is no individual in ontology
	private Set<OWLClassExpression> rightConjunctsOfTop = null;
	//0 : breadth; 1 : depth; 2 : both
	private int strategy = 0;
	public ReasoningData()
	{
		initABox = new ABox();
		initialAtomicConcepts = new HashSet<OWLClass>();
		derivedAtomicConcepts = new HashSet<OWLClass>();
		superClosureByRole = HashMultimap.create();
		subClosureByRole = HashMultimap.create();
		absorbedSupersBySub = HashMultimap.create();
		absorbedAtomic = new HashSet<OWLClassExpression> ();
		absorbedNegated = new HashSet<OWLClassExpression> ();
	//	setIRIBase( Optional.fromNullable((IRI.create("http://iut.univ-paris8.fr/linc/myOnto") ))) ;
		setTop(factory.getOWLThing());
		setBottom(factory.getOWLNothing());
		minNames = new HashMap<OWLClassExpression,List<OWLClass>>();
		rightConjunctsOfTop = new HashSet<OWLClassExpression>();
		//the keys of the two following maps contain all role names
		objectPropWithAttr = new HashMap<OWLObjectPropertyExpression, RoleAttributes>();
		dataPropWithAttr = new HashMap<OWLDataPropertyExpression, RoleAttributes>();
	}

	public LKBox getLKBox()
	{
		return LK;
	}

	public ABox getABox()
	{
		return initABox;
	}

	public int getNewIndividualID()
	{
		return individualID++;
	}

	public int getNewConceptID()
	{
		return conceptID++;
	}

	public Optional<IRI> getIRIBase(){
		return IRIBase;
	}

	public void setIRIBase(Optional<IRI> iri)
	{
		IRIBase = iri;
	}

	public void setDummyInd()
	{
		//dummyInd = factory.getOWLNamedIndividual(IRI.create("http://http://iut.univ-paris8.fr/linc/owl#Individual_"+  getNewIndividualID()) );
	}

	public OWLIndividual getDummyInd()
	{
		return dummyInd;
	}

	public Triple getDummyTriple(ConceptLabel core, ConceptLabel tip)
	{
		Ray ray = new Ray( new RoleLabel(), tip);
		Triple triple =  new Triple(core, ray) ;
		return triple;
	}

	public boolean isDummyTriple(Triple triple)
	{
		if(triple.getRay().getRidge().getRoles().isEmpty())
			return true;
		else
			return false;
	}

	public int getStrategy()
	{
		return strategy;
	}

	public void setStrategy(int s)
	{
		strategy = s;
	}
	public Set<OWLClass> getInitialAtomicConcepts()
	{
		return initialAtomicConcepts;

	}
	public Set<OWLClass> getDerivedAtomicConcepts()
	{
		return derivedAtomicConcepts;

	}
	public Set<OWLClass> getAllAtomicConcepts()
	{
		return Sets.union(getDerivedAtomicConcepts(), getInitialAtomicConcepts());

	}
	public Map<OWLObjectPropertyExpression, RoleAttributes> getObjectPropWithAttr()
	{
		return objectPropWithAttr;
	}
	public Map<OWLDataPropertyExpression, RoleAttributes> getDataPropWithAttr()
	{
		return dataPropWithAttr;
	}
	public Set<OWLClassExpression> getAbsorbedAtomic()
	{
		return absorbedAtomic;
	}
	public void setAbsorbedAtomic(Set<OWLClassExpression> ab)
	{
		absorbedAtomic = ab;
	}
	public Set<OWLClassExpression> getAbsorbedNegated()
	{
		return absorbedNegated;
	}
	public void setAbsorbedNegated(Set<OWLClassExpression> ab)
	{
		absorbedNegated = ab;
	}

	public SetMultimap<BinaryLabel, OWLClassExpression> getAbsorbedSupersBySub()
	{
		return absorbedSupersBySub;
	}

	public void setAbsorbedSupersBySub(SetMultimap<BinaryLabel, OWLClassExpression> ab)
	{
		absorbedSupersBySub = ab;
	}

	public void setSuperClosureByRole(SetMultimap<OWLPropertyExpression, OWLPropertyExpression> superR)
	{
		superClosureByRole = superR;
	}
	public void setSubClosureByRole(SetMultimap<OWLPropertyExpression, OWLPropertyExpression> subR)
	{
		subClosureByRole = subR;
	}

	public OWLObjectOneOf getOWLObjectOneOf(Set<OWLIndividual> inds)
	{
		return factory.getOWLObjectOneOf(inds);
	}

	/*
	 * Called by Frame.createInitNominalSharedStartypes
	 * Adds concepts from the axioms by internalization
	 * Uses the initABox
	 */
	// This is  like the function init, it returns  one single star-type
	// It takes a set because, is it because of equal individuals?
	public Startype createInitStartype(Set<OWLIndividual> inds)
	{
		Startype st = null;
		Set<OWLClassExpression> concepts = new HashSet<OWLClassExpression>();

		if(inds!=null)
		{
			for(OWLIndividual i : inds)
			{
				concepts.addAll(initABox.getConceptsByInd().get(i)); //get concept assertions
				//	initABox.getConceptsByInd().get(i);

				//conjunction of individuals
				//	for(OWLIndividual j : initABox.getClosureByInd().get(i))
				//  concepts.add(factory.getOWLObjectOneOf(j));
			}
			//System.out.println(concepts);
		}
		concepts = this.getConceptsFromPrimitiveAxioms(concepts, new HashSet<OWLClassExpression>());
	//	System.out.println(concepts);
		//  Set<OWLClassExpression>  i=this.getInitCore().getConcepts();


		if(this.getInitCore().getConcepts().isEmpty())
		{

			ConceptLabel cl = new ConceptLabel(concepts);
			st = new Startype(cl, this );
		}
		else
		{
			Set<OWLClassExpression> ids = new HashSet<OWLClassExpression> (this.getInitCore().getConcepts());
			ids.addAll(concepts);
			ConceptLabel cl = new ConceptLabel(ids);
			st = new Startype(cl, this);


		}
		st.addFreshCore(st.getCore().getConcepts(), this );

		return st;
	}

	public void neighbourhood (Startype st, OWLOntology ontology, ABox a,PrefixManager pmanager ) {
		Set<OWLIndividual> inds=st.getCore().getIndividual();

		for (OWLIndividual ind: inds) {


			SetMultimap<OWLIndividual, Map<OWLObjectPropertyExpression, OWLIndividual>> assertions=a.getConceptObjAssertsBySource();


			for( Entry<OWLIndividual, Map<OWLObjectPropertyExpression, OWLIndividual>> ass:assertions.entries()) {
				if(ass.getKey()==ind) {

					for(Map<OWLObjectPropertyExpression, OWLIndividual> m: assertions.get(ind))
					{


						Triple tr=new Triple();
						Set<OWLIndividual> set_ind=new HashSet();
						// the individuals of the head of the triple are the same as the core of the star-type
						tr.setCoreI(st.getCore().getIndividual());

						//New set for the properties
						Set<OWLPropertyExpression> trp=new HashSet<OWLPropertyExpression>();
						Set<OWLObjectPropertyExpression> p=m.keySet();
						OWLObjectProperty ps = factory.getOWLObjectProperty(p.toString().substring(2,3),pmanager);
						//System.out.println("Here "+ps);
						trp.add(ps);
						tr.addRolesToRay(trp);

						Set<OWLIndividual> o =new HashSet();
						for(OWLObjectPropertyExpression pp:p)
						{o.add( m.get(pp));

						}
						//tr.getRay().setTip(o);
						tr.getRay().getTip().setIndividual(o);
						LinkedHashSet<OWLClassExpression> f =new LinkedHashSet<OWLClassExpression>();
						for(OWLIndividual i:o) {

							set_ind.add(i);
							f.addAll(a.getConceptsByInd().get(i));

						}
						tr.getRay().getTip().setConcepts(f);
						tr.getRay().getTip().setIndividual(set_ind);
						st.addTriple(tr);

					}
				}
			}
		}
	}
	/*
	 * Used when adding an individual to the  tip  of a ray
	 * Uses the initABox
	 */
	public Set<OWLClassExpression> getConceptsForIndividuals(Set<OWLIndividual> inds)
	{
		Set<OWLClassExpression> concepts = null;
		if( inds!=null )
		{
			for(OWLIndividual i : inds) {
				concepts = initABox.getConceptsByInd().get(i); //get concept assertions
				
			}
		} else
		{
			concepts =  new HashSet<OWLClassExpression>();
		}
		concepts = this.getConceptsFromPrimitiveAxioms(concepts, new HashSet<OWLClassExpression>());
		
		if(this.getInitCore().getConcepts().size()==0)
		{
			if(inds!=null)
			{
				concepts.add(getOWLObjectOneOf(inds));
			}
		}
		else
		{
			Set<OWLClassExpression> ids = new HashSet<OWLClassExpression> (this.getInitCore().getConcepts());
			ids.addAll(concepts );
			if(inds!=null)
			{
				concepts.add(getOWLObjectOneOf(inds));
			}

		}
		
		return concepts;
	}

	public Set<OWLClassExpression> computeOntoDisjunction(Set<OWLClassExpression> cs)
	{
		//System.out.println("cs="+ (new ConceptLabel(cs)).toString());
		//Scanner scan = new Scanner(System.in);
		//String text= scan.nextLine();
		Set<OWLClassExpression> sOs = new HashSet<OWLClassExpression>();
		for(OWLClassExpression conj : cs)
		{
			if(conj.getClassExpressionType()== ClassExpressionType.OBJECT_UNION_OF){
				Set<OWLClassExpression> disjuncts = conj.asDisjunctSet();
				for(OWLClassExpression co : disjuncts){
					Set<OWLClassExpression> newConj = new HashSet<OWLClassExpression>(cs);
					newConj.remove(conj);
					Set<OWLClassExpression> ss = computeOntoDisjunction(newConj);
					ss.add(co);
					sOs.addAll(ss);
				}
			}else {
				sOs.add(conj);
			}
		}

		return sOs;
	}


	/*
	 * Serves to lazy rule application and to discover clash early
	 * Applies lazy folding to binary and atomic axioms stored in "getAbsorbedSuperBySub"
	 *
	 */
	public Set<OWLClassExpression> getConceptsFromPrimitiveAxioms(Set<OWLClassExpression> concepts, Set<OWLClassExpression> existings )
	{
		Set<OWLClassExpression> toAdd = new HashSet<OWLClassExpression>(concepts);

		toAdd.addAll( existings );
		toAdd.addAll(this.getRightConjunctsOfTop());//\top < C
//System.out.println(this.getRightConjunctsOfTop());
		boolean changed = true;
		while(changed)
		{
			changed = false;
			for(BinaryLabel cs : this.getAbsorbedSupersBySub().keySet() )
			{
				

				if( toAdd.containsAll( cs.getBoth() )  && !toAdd.containsAll( this.getAbsorbedSupersBySub().get(cs) ) )
				{
					toAdd.addAll(  this.getAbsorbedSupersBySub().get( cs ) );
					changed = true;
				}
			}
		}

		toAdd.remove(getTop());
		
		return toAdd;
	}


	//Checks if "cs1" has a clash with "cs2", assume that has no clash 
	public boolean isL1LiteralExpression(OWLClassExpression concept)
	{
		if(concept.isAnonymous())
		{
		
			if( concept.getClassExpressionType() == ClassExpressionType.OBJECT_ALL_VALUES_FROM ||
					concept.getClassExpressionType() == ClassExpressionType.OBJECT_SOME_VALUES_FROM ||
					concept.getClassExpressionType() == ClassExpressionType.OBJECT_MIN_CARDINALITY )
			{
				OWLClassExpression filler = (OWLClassExpression)((OWLQuantifiedRestriction)concept).getFiller();
				if(filler.isClassExpressionLiteral())
					return true;
				else
					return false;
			} else
				return false;
		} else
			return false;
	}


	public boolean isAllL1LiteralExpression(OWLClassExpression concept)
	{
		if(concept.isAnonymous())
		{
			if( concept.getClassExpressionType() == ClassExpressionType.OBJECT_ALL_VALUES_FROM )
			{
				OWLClassExpression filler = (OWLClassExpression)((OWLQuantifiedRestriction)concept).getFiller();
				if(filler.isClassExpressionLiteral())
					return true;
				else
					return false;
			} else
				return false;
		} else
			return false;
	}
	//Not for ALC

	public boolean isMinL1LiteralExpression(OWLClassExpression concept)
	{
		if(concept.isAnonymous())
		{
			if( concept.getClassExpressionType() == ClassExpressionType.OBJECT_SOME_VALUES_FROM ||
					concept.getClassExpressionType() == ClassExpressionType.OBJECT_MIN_CARDINALITY )
			{
				OWLClassExpression filler = (OWLClassExpression)((OWLQuantifiedRestriction)concept).getFiller();
				if(filler.isClassExpressionLiteral())
					return true;
				else
					return false;
			} else
				return false;
		} else
			return false;
	}

	public boolean isSomeL1LiteralExpression(OWLClassExpression concept)
	{
		if(concept.isAnonymous())
		{
			if( concept.getClassExpressionType() == ClassExpressionType.OBJECT_SOME_VALUES_FROM )
			{
				OWLClassExpression filler = (OWLClassExpression)((OWLQuantifiedRestriction)concept).getFiller();
				if(filler.isClassExpressionLiteral())
					return true;
				else
					return false;
			} else
				return false;
		} else
			return false;
	}

	public boolean isL1Clash(OWLClassExpression c1, OWLClassExpression c2 ) {
		if( !this.isL1LiteralExpression(c1) || !this.isL1LiteralExpression(c2))
			return false;
		if( (this.isAllL1LiteralExpression(c1) && this.isAllL1LiteralExpression(c2)) ||
				(!this.isAllL1LiteralExpression(c1) && !this.isAllL1LiteralExpression(c2)) )
			return false;

		OWLPropertyExpression r1 = ((OWLQuantifiedRestriction)c1).getProperty();
		OWLPropertyExpression r2 = ((OWLQuantifiedRestriction)c2).getProperty();
		if(!r1.equals(r2))
			return false;

		OWLClassExpression co1 = (OWLClassExpression)((OWLQuantifiedRestriction)c1).getFiller();
		OWLClassExpression co2 = (OWLClassExpression)((OWLQuantifiedRestriction)c2).getFiller();
		if( !co1.isClassExpressionLiteral() || !co2.isClassExpressionLiteral() )
			return false;
		if( !co1.isAnonymous() && !co2.isAnonymous())
			return false;
		if( co1.isAnonymous() ){
			OWLClassExpression name = ((OWLObjectComplementOf)co1).getOperand();
			if(name.equals(co2))
				return true;
		}else {
			OWLClassExpression name = ((OWLObjectComplementOf)co2).getOperand();
			if(name.equals(co1))
				return true;
		}
		return false;
	}

	public SetMultimap<OWLPropertyExpression, OWLPropertyExpression> getSuperClosureByRole()
	{
		return superClosureByRole;
	}
	public SetMultimap<OWLPropertyExpression, OWLPropertyExpression> getSubClosureByRole()
	{
		return subClosureByRole;
	}

	public void setInitCore(ConceptLabel co)
	{
		initCore = co;
	}

	public ConceptLabel getInitCore( )
	{
		return initCore ;
	}

	public ConceptLabel getEmptyCore() {
		return emptyCore;
	}

	public void setEmptyCore(ConceptLabel co)
	{
		emptyCore = co;
	}

	public void setRightConjunctsOfTop(Set<OWLClassExpression> conj)
	{
		rightConjunctsOfTop = conj;
	}

	public Set<OWLClassExpression> getRightConjunctsOfTop()
	{
		return rightConjunctsOfTop;
	}


	public void setTop(OWLClass  c)
	{
		top = c;
	}

	public OWLClass  getTop()
	{
		return top;
	}
	public void setBottom(OWLClass c)
	{
		bottom = c;
	}
	public OWLClass  getBottom()
	{
		return bottom;
	}

	// It is possible that a tip coincides with core ( e.g. R(o,o) )
	// We don't need existName because if there are \exists R. A, \exists R. B, \forall R. (A \sqcap B)
	//  one ray is maintained due to set of rays
	public void setNameForMIN(OWLClassExpression concept)
	{
		String inverse ="";
		String transitive ="";
		String closure ="";
		String roleName = null ;
		int card = 0;
		OWLPropertyExpression owlRole = null;
		if(concept instanceof OWLDataMinCardinality) {
			owlRole =  ((OWLDataMinCardinality)concept).getProperty();
			roleName = ((OWLDataPropertyExpression)owlRole).asOWLDataProperty().getIRI().toString();
			roleName = roleName.substring(roleName.indexOf("#") + 1);
			card = ((OWLDataMinCardinality)concept).getCardinality();
		}
		else if(concept instanceof OWLObjectMinCardinality)   {
			owlRole = ((OWLObjectMinCardinality)concept).getProperty();
			roleName = ((OWLObjectPropertyExpression)owlRole).getNamedProperty().getIRI().toString();
			roleName = roleName.substring(roleName.indexOf("#") + 1);
			inverse = (owlRole instanceof OWLObjectInverseOf) ? "_INVERSE" : "";
			transitive =  getObjectPropWithAttr().get(owlRole).isTransitive() ? "_TRANSITIVE" : "";
			card = ((OWLObjectMinCardinality)concept).getCardinality();
		} else
			return;


		List<OWLClass> sMin = new ArrayList<OWLClass>(card);
		//OWLDataFactory factory = new OWLDataFactoryImpl();
		for(int i=0 ; i< card ;i++){
			String name = "http://linc/owl#MIN_" + card + inverse +  transitive + roleName+  "_" +i; //??? baseIRI ?
			// It is always a new OWLClass
			OWLClass cls = factory.getOWLClass( IRI.create( name ) );
			sMin.add( cls );
		}
		minNames.put(concept, sMin);
	}

	public List<OWLClass> getMinNames(OWLClassExpression concept)
	{
		if (minNames.containsKey(concept))
			return minNames.get(concept);
		else {
			this.setNameForMIN(concept);
			return minNames.get(concept);
		}
	}


	/* It checks transitivity in the transitive closure of role hierarchy */
	public boolean isTransive(OWLPropertyExpression role)
	{
		Set<OWLPropertyExpression> subs = this.getSubClosureByRole().get(role);
		for (OWLPropertyExpression r :  subs  )
			if ( (r instanceof OWLObjectPropertyExpression) &&  this.getObjectPropWithAttr().get(r).isTransitive()  )
				return true;
		return false;
	}

	//Not needed for ALC
	// Finds all sub transitive roles of "role"
	public Set<OWLPropertyExpression> getRolesForTransRule(OWLPropertyExpression role){
		Set<OWLPropertyExpression> roles = new HashSet<OWLPropertyExpression>( this.getSubClosureByRole().get(role) );
		//It was a bug here : role was always is transitive  (roles1 was not added : 31/11/2015
		Set<OWLPropertyExpression> roles1 = new HashSet<OWLPropertyExpression>();
		for(OWLPropertyExpression r : roles){
			if ( (r instanceof OWLObjectPropertyExpression) && this.getObjectPropWithAttr().get(r).isTransitive() )
				roles1.add( r );
		}
		return roles1;
	}

	public OWLClassExpression getTransObjectAllValuesFrom(OWLPropertyExpression trans, OWLClassExpression filler){
		//OWLDataFactory factory = new OWLDataFactoryImpl();
		return factory.getOWLObjectAllValuesFrom( (OWLObjectPropertyExpression)trans, filler);
	}

	public boolean isSimple(OWLPropertyExpression role) {
		Set<OWLPropertyExpression> subs = this.getSubClosureByRole().get( role );
		for (OWLPropertyExpression ex : subs)
			if ( (ex instanceof  OWLObjectPropertyExpression) &&  this.getObjectPropWithAttr().get(ex).isTransitive(  ) )
				return false;
		return true;
	}

	public Map<OWLClassExpression, List<OWLClass>> getMinNames()
	{
		return minNames;
	}

	public int getIndividualID() {
		return individualID;
	}

	public int getConceptID() {
		return conceptID;
	}
	public void setUnion(boolean v){
		containsUnion = v;
	}
	public boolean getUnion(){
		return containsUnion ;
	}
	public void containsLk(boolean v) {
		containsLk = v;

	}

	public void setNominal(boolean v){
		containsNominal = v;
	}
	public boolean getNominal(){
		return containsNominal ;
	}

	public void setSome(boolean v){
		containsSome = v;
	}
	public boolean getSome(){
		return containsSome ;
	}

	public void setCardinality(boolean v){
		containsCardinality = v;
	}
	public boolean getCardinality(){
		return containsCardinality;
	}

	public void setTransitive(boolean v){
		containsTransitive = v;
	}
	public boolean getTransitive(){
		return containsTransitive ;
	}

	public void setInverse(boolean v){
		containsInverse = v;
	}
	public boolean getInverse(){
		return containsInverse ;
	}
	public void setABox(ABox A){
		this.initABox=A;
	}

	public void setDatatype(boolean v){
		containsDatatype = v;
	}
	public boolean getDatatype(){
		return containsDatatype ;
	}

	public void setHierarchy(boolean v){
		containsHierarchy = v;
	}
	public boolean getHierarchy(){
		return containsHierarchy ;
	}

	public void setLK(LKBox lk) {
		// TODO Auto-generated method stub
		LK=lk;

	}

	public static OWLDataFactory getFactory() {
		return factory;
	}

	public static void setFactory(OWLDataFactory factory) {
		ReasoningData.factory = factory;
	}
}
