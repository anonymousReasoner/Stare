package fr.anonymous.reasoner;
import com.google.common.collect.SetMultimap;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLIndividual;
import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;

import java.util.*;
import java.util.stream.Collectors;

public class Linkey {
	private StartypePair pairsOfLk;

	public StartypePair getPairsOfLk() {
		return pairsOfLk;
	}
	public void setPairsOfLk(StartypePair pairsOfLk) {
		this.pairsOfLk = pairsOfLk;
	}
	private  ConceptPair PairsOfConcepts;

	private Set<PropertyPair> PropertySet ;

	public Linkey(ConceptPair pairsOfConcepts, Set<PropertyPair> propertySet) {
		this.PairsOfConcepts = pairsOfConcepts;
		this.PropertySet = propertySet;
	}
	public Linkey() {

	}
	public ConceptPair getPairsOfConcepts() {
		return PairsOfConcepts;
	}
	public void setPairsOfConcepts(ConceptPair pairsOfConcepts) {
		this.PairsOfConcepts = pairsOfConcepts;
	}
	public Set<PropertyPair> getPropertySet() {
		return PropertySet;
	}
	public void setPropertySet(Set<PropertyPair> propertySet) {
		this.PropertySet = propertySet;
	}
	public boolean weakSatisfaction(Startype s_1,  Startype s_2,   Linkey lk)
	{
		//

		List<Triple> triples_1=s_1.getTriples();
		List<Triple> triples_2=s_2.getTriples();
		Set<PropertyPair> role=lk.getPropertySet();
		Set<Set<Startype>> toReturn=new HashSet<>();
		for(Triple tr_1 :triples_1 ) {

			for( Triple tr_2 :triples_2) {

				for(PropertyPair pp : role) {
					//System.out.println("First property of the link key " +pp.getFirstProperty() + "Second property of the link key " +pp.getSecondProperty() );
					for(Succ o1:s_1.getSucc().getMatch().stream().filter(o -> o.getT().equals(tr_1)).collect(Collectors.toSet())) {
						for(Succ o2:s_2.getSucc().getMatch().stream().filter(o -> o.getT().equals(tr_2)).collect(Collectors.toSet())) {

							//	System.out.println("triple 2 roles:"+tr_2.getRay().getRidge().getRoles()+", lk roles "+pp.getSecondProperty());
							if ((tr_2.getRay().getRidge().getRoles().contains(pp.getSecondProperty()) || tr_2.getRay().getRidge().getRoles().containsAll(Collections.singleton(pp.getSecondProperty()))) &&
									(tr_1.getRay().getRidge().getRoles().contains(pp.getFirstProperty()) || tr_1.getRay().getRidge().getRoles().containsAll(Collections.singleton(pp.getFirstProperty())))) {
								//Here should be different
								//System.out.println(tr_1.getRay().getTip().getIndividual().toString());
								//	System.out.println(tr_2.getRay().getTip().getIndividual().toString());


								if (tr_1.getRay().getTip().getIndividual().toString().equals(tr_2.getRay().getTip().getIndividual().toString())||tr_1.getRay().getTip().getIndividual().toString().contains(tr_2.getRay().getTip().getIndividual().toString())) {

									System.out.println("The tips of the triples are equal");
									return true;
								}
								if (o1.getSset().equals(o2.getSset()) || o1.getSset().containsAll(o2.getSset())) {
									System.out.println("The star-types are matched to the same set of star-types");
									Set<Startype> set=new HashSet<>();
									set.add(s_1);
									set.add(s_2);
									set.addAll(o1.getSset());
									toReturn.add(set);
									return true;
								}
							}
						}
					}
				}
			}
		}
		//this.lk=toReturn;

		return false;
	}
	//done
	public boolean strongSatisfaction(Startype s_1,  Startype s_2,  Linkey lk)
	{
		//	System.out.println("Inside strong satisfaction");
		return weakSatisfaction( s_1,   s_2,  lk)&&(s_1.getCore().getConcepts().contains((lk.getPairsOfConcepts().getFirstConcept()))||s_1.getCore().getConcepts().equals(lk.getPairsOfConcepts().getFirstConcept())) && (s_2.getCore().getConcepts().contains(lk.getPairsOfConcepts().getSecondConcept()) ||  s_2.getCore().getConcepts().equals(lk.getPairsOfConcepts().getSecondConcept()));
	}


	public boolean lkRule(Startype s_1,  Startype s_2,   Linkey lk)
	{

		return strongSatisfaction( s_1,   s_2,   lk);
	}

	public Startype chlk_1Rule(Startype s_1,  Startype s_2,  ReasoningData data, Linkey lk)
	{ //Check if they weakly satisfy the condition of a lk
		System.out.println("Inside chlk_1 ");
		if(!s_1.equals(s_2)) {
			Startype copyS_1 = new Startype();
			copyS_1.setCore(s_1.getCore(), data);
			copyS_1.setTriples(s_1.getTriples());

			OWLDataFactory df = new OWLDataFactoryImpl();

			if ((weakSatisfaction(s_1, s_2, lk) && !copyS_1.getCore().getConcepts().contains(lk.getPairsOfConcepts().getFirstConcept()) &&
					!copyS_1.getCore().getConcepts().contains(lk.getPairsOfConcepts().getFirstConcept().getObjectComplementOf())
					&& !copyS_1.getCore().getConcepts().contains(df.getOWLObjectUnionOf(lk.getPairsOfConcepts().getFirstConcept(), lk.getPairsOfConcepts().getFirstConcept().getObjectComplementOf())) && !copyS_1.getCore().getConcepts().equals(lk.getPairsOfConcepts().getFirstConcept()) &&
					!copyS_1.getCore().getConcepts().equals(lk.getPairsOfConcepts().getFirstConcept().getObjectComplementOf())
					&& !copyS_1.getCore().getConcepts().equals(df.getOWLObjectUnionOf(lk.getPairsOfConcepts().getFirstConcept(), lk.getPairsOfConcepts().getFirstConcept().getObjectComplementOf())))) {

				copyS_1.getCore().add(df.getOWLObjectUnionOf(lk.getPairsOfConcepts().getFirstConcept(), lk.getPairsOfConcepts().getFirstConcept().getObjectComplementOf()));
				return copyS_1;

			}

		}

		return null;




	}



	public Startype chlk_2Rule(Startype s_1,  Startype s_2,  ReasoningData data, Linkey lk)
	{ //Check if they weakly satisfy the condition of a lk
		System.out.println("Inside chlk_2 ");
		if(!s_1.equals(s_2)) {
			Startype copyS_2 = new Startype();
			copyS_2.setCore(s_2.getCore(), data);
			copyS_2.setTriples(s_2.getTriples());


			OWLDataFactory df = new OWLDataFactoryImpl();
			//&&s_2.isSecond() &&!s_1.isFirst()
			//%!copyS_2.getCore().getConcepts().contains(lk.getPairsOfConcepts().getSecondConcept().getObjectComplementOf()) &&
			System.out.println(lk.getPairsOfConcepts().getSecondConcept());
			if (weakSatisfaction(s_1, s_2, lk) && !strongSatisfaction(s_1, s_2, lk) && !copyS_2.getCore().getConcepts().contains(lk.getPairsOfConcepts().getSecondConcept()) &&

					!copyS_2.getCore().getConcepts().contains(df.getOWLObjectUnionOf(lk.getPairsOfConcepts().getSecondConcept(), lk.getPairsOfConcepts().getSecondConcept().getObjectComplementOf()))&&
					!copyS_2.getCore().getConcepts().equals(lk.getPairsOfConcepts().getSecondConcept())
					&&
					!copyS_2.getCore().getConcepts().equals(lk.getPairsOfConcepts().getSecondConcept().getObjectComplementOf()) &&
					!copyS_2.getCore().getConcepts().equals(df.getOWLObjectUnionOf(lk.getPairsOfConcepts().getSecondConcept(), lk.getPairsOfConcepts().getSecondConcept().getObjectComplementOf()))
			) {

				copyS_2.getCore().add(df.getOWLObjectUnionOf(lk.getPairsOfConcepts().getSecondConcept(), lk.getPairsOfConcepts().getSecondConcept().getObjectComplementOf()));

				return copyS_2;

			}
		}

		return null;

	}

	public boolean shouldMerge(Startype s_1,  Startype s_2,  ReasoningData data) {
		boolean shouldMerge=false;

		if(!s_1.equals(s_2)) {
			Set<OWLIndividual> coreIndividuals_1 = s_1.getCore().getIndividual();

			Set<OWLIndividual> coreIndividuals_2 = s_2.getCore().getIndividual();
			Iterator<OWLIndividual> arbInd_1 = coreIndividuals_1.iterator();
			Iterator<OWLIndividual> arbInd_2 = coreIndividuals_2.iterator();
			SetMultimap<OWLIndividual, OWLIndividual> sameIndAssers = data.getABox().getSameIndAssers();
			//check if the equality assertion does not exist in the abox
			OWLIndividual ind_1, ind_2;
			while (arbInd_1.hasNext()) {
				ind_1 = arbInd_1.next();
				while (arbInd_2.hasNext()) {
					ind_2 = arbInd_2.next();
					if (sameIndAssers.containsEntry(ind_1, ind_2) && !isMergeContained(s_1, s_2)) {

						shouldMerge = true;

					}
				}
			}
			for (Linkey lk : data.getLKBox().getLks()) {
				if (strongSatisfaction(s_1, s_2, lk)&&!isMergeContained(s_1,s_2) ) {

					shouldMerge = true;
				}
			}
		}

		return shouldMerge;
	}
	public boolean isMergeContained(Startype s_1,  Startype s_2) {
		for(Startype s:s_1.getAddress().getSstar()) {
			//R-neighbourhood relation
			if(s.getCore().getIndividual().contains(s_1.getCore().getIndividual())&&s.getCore().getIndividual().contains(s_2.getCore().getIndividual())&&s.getCore().getConcepts().contains(s_1.getCore().getConcepts())&&s.getCore().getConcepts().contains(s_2.getCore().getConcepts())) {
				System.out.println(s.getCore().getIndividual());
				//	System.out.println(s.getCore().getIndividuals());
				return true;
			}
		}
		return false;

	}


	public Set<Startype> merge(Startype s_1,  Startype s_2,  ReasoningData data) {

		Set<Startype> merges=new HashSet<>();
		Startype merge1=new Startype();
		Startype merge2=new Startype();
		List<Triple> triples_1=s_1.getTriples();
		List<Triple> triples_2=s_2.getTriples();

		LinkedHashSet<OWLClassExpression> merge_concepts=new LinkedHashSet<>();
		merge_concepts.addAll(s_1.getCore().getConcepts());
		merge_concepts.addAll(s_2.getCore().getConcepts());
		Set<OWLIndividual> merge_inds=new HashSet<>();
		merge_inds.addAll(s_1.getCore().getIndividual());
		merge_inds.addAll(s_2.getCore().getIndividual());
		ConceptLabel cl=new ConceptLabel(merge_concepts,merge_inds);
		merge1.setCore(cl, data);
		merge2.setCore(cl, data);
		for(Triple tr_1 :triples_1) {
			tr_1.addConceptsToCore(merge1.getCore().getConcepts());
			merge1.addTriple(tr_1);
		}
		for( Triple tr_2 :triples_2) {
			tr_2.addConceptsToCore(merge2.getCore().getConcepts());
			merge2.addTriple(tr_2);
		}
		merges.add(merge1);
		merges.add(merge2);
		System.out.println(merge1.getCore().getIndividual());
		System.out.println(merge2.getCore().getIndividual());
		return merges;
	}


	/*
	 *  Apply the union (\sqcup) rule to "concept" (that must be a \sqcup-concept) in the core of the startype.
	 *  Create a new backtracking point as new unsat startype with history
	 * "his" of "this" is not explicitly changed since "updateCore" updates automatically
	 */
	public boolean isLkRuleApp(Startype s1, Startype s2, LKBox LK, ReasoningData data){
		for(Linkey lk:LK.getLks()) {
			if((weakSatisfaction(s1, s2, lk)&&!strongSatisfaction(s1, s2, lk))||shouldMerge(s1, s2, data)) {
				return true;
			}
		}
		return false;
	}



}
