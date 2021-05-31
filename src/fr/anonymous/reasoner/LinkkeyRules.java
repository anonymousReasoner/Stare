package fr.anonymous.reasoner;


import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLIndividual;

import com.google.common.collect.SetMultimap;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;

//After that you can implement the reasoning core by using all ALC rules  from Startype.java, and all  LK rules from "LinkkeyRules.java".  I suggest that you test carefully each method when you finish it.

public class LinkkeyRules implements StartypeOperators{


	public boolean weakSatisfaction(Startype s_1,  Startype s_2,   Linkey lk, MatchingFn mf)
	{

		List<Triple> triples_1=s_1.getTriples(), triples_2=s_2.getTriples();


		Set<PropertyPair> role=lk.getPropertySet();
		
		//  System.out.println(s_2.getCore().getIndividual());
		for(Triple tr_1 :triples_1 ) {

			for( Triple tr_2 :triples_2) {

				for(PropertyPair pp : role) {
				
					
						for(Omega o1:mf.getMatch()) {
							for(Omega o2:mf.getMatch()) {
							if(o1.getS().equals(s_1)&&o1.getT().equals(tr_1)&&(tr_1.getRay().getRidge().getRoles().contains(pp.getFirstProperty()))) {
							
							
								if(o2.getS().equals(s_2)&&o2.getT().equals(tr_2)&&(tr_2.getRay().getRidge().getRoles().contains(pp.getSecondProperty()))) {
								if(o1.getSset().equals(o2.getSset())) {
									if(s_1.getAddress().getSstar().containsAll(o1.getSset()))
							//			System.out.println("These two star-types weakly satisfy"+s_1.getCore().toString()+" and "+s_2.getCore().toString());
									return true;
								}
								}
								
							}
						}

						}
					}
					}}
		return false;
	}
	//done
	public boolean strongSatisfaction(Startype s_1,  Startype s_2,  Linkey lk, MatchingFn mf)
	{
		if (weakSatisfaction( s_1,   s_2,  lk, mf))

			if((s_1.getCore().getConcepts().contains((lk.getPairsOfConcepts().getFirstConcept()))||s_1.getCore().getConcepts().equals(lk.getPairsOfConcepts().getFirstConcept())) && (s_2.getCore().getConcepts().contains(lk.getPairsOfConcepts().getSecondConcept()) ||  s_2.getCore().getConcepts().equals(lk.getPairsOfConcepts().getSecondConcept())))
			//	System.out.println("These two star-types strongly satisfy"+s_1.getCore().toString()+" and "+s_2.getCore().toString());
				return true;
		return false;
	}


	public boolean lkRule(Startype s_1,  Startype s_2,   Linkey lk, MatchingFn mf)
	{
		if(strongSatisfaction( s_1,   s_2,   lk, mf)) return true;
		return false;
	}

	public Startype chlk_1Rule(Startype s_1,  Startype s_2,  ReasoningData data, Linkey lk,  MatchingFn mf)
	{ //Check if they weakly satisfy the condition of a lk
		Startype copyS_1=new Startype();
		copyS_1.setCore(s_1.getCore(),data);
		copyS_1.setTriples(s_1.getTriples());

		OWLDataFactory df= new OWLDataFactoryImpl();

		if(weakSatisfaction( s_1,   s_2,     lk, mf)&&!strongSatisfaction( s_1,   s_2,     lk, mf) ){
	
			if(!copyS_1.getCore().getConcepts().contains(lk.getPairsOfConcepts().getFirstConcept())&&
					!copyS_1.getCore().getConcepts().contains(lk.getPairsOfConcepts().getFirstConcept().getObjectComplementOf())
					&&!copyS_1.getCore().getConcepts().contains(df.getOWLObjectUnionOf (lk.getPairsOfConcepts().getFirstConcept(), lk.getPairsOfConcepts().getFirstConcept().getObjectComplementOf()))&&!copyS_1.getCore().getConcepts().equals(lk.getPairsOfConcepts().getFirstConcept())&&
					!copyS_1.getCore().getConcepts().equals(lk.getPairsOfConcepts().getFirstConcept().getObjectComplementOf())
					&&!copyS_1.getCore().getConcepts().equals(df.getOWLObjectUnionOf (lk.getPairsOfConcepts().getFirstConcept(), lk.getPairsOfConcepts().getFirstConcept().getObjectComplementOf()))) {

				copyS_1.getCore().add( df.getOWLObjectUnionOf (lk.getPairsOfConcepts().getFirstConcept(), lk.getPairsOfConcepts().getFirstConcept().getObjectComplementOf()));
				return copyS_1;
			}
		}



		return null;




	}



	public Startype chlk_2Rule(Startype s_1,  Startype s_2,  ReasoningData data, Linkey lk,  MatchingFn mf)
	{ //Check if they weakly satisfy the condition of a lk
		Startype copyS_2=new Startype();
		copyS_2.setCore(s_2.getCore(),data);
		copyS_2.setTriples(s_2.getTriples());


		OWLDataFactory df= new OWLDataFactoryImpl();
		//&&s_2.isSecond() &&!s_1.isFirst()
		if(weakSatisfaction( s_1,   s_2,     lk, mf)&&!strongSatisfaction( s_1,   s_2,     lk, mf)&&!copyS_2.getCore().getConcepts().contains(lk.getPairsOfConcepts().getSecondConcept())&&
				!copyS_2.getCore().getConcepts().contains(lk.getPairsOfConcepts().getSecondConcept().getObjectComplementOf())&&
				!copyS_2.getCore().getConcepts().contains(df.getOWLObjectUnionOf (lk.getPairsOfConcepts().getSecondConcept(), lk.getPairsOfConcepts().getSecondConcept().getObjectComplementOf()))
				&&!copyS_2.getCore().getConcepts().equals(lk.getPairsOfConcepts().getSecondConcept())&&
				!copyS_2.getCore().getConcepts().equals(lk.getPairsOfConcepts().getSecondConcept().getObjectComplementOf())&&
				!copyS_2.getCore().getConcepts().equals(df.getOWLObjectUnionOf (lk.getPairsOfConcepts().getSecondConcept(), lk.getPairsOfConcepts().getSecondConcept().getObjectComplementOf()))) {

			copyS_2.getCore().add( df.getOWLObjectUnionOf (lk.getPairsOfConcepts().getSecondConcept(), lk.getPairsOfConcepts().getSecondConcept().getObjectComplementOf()));

			return copyS_2;

		}


		return null;

	}

	public boolean shouldMerge(Startype s_1,  Startype s_2,  ReasoningData data, MatchingFn mf) {
		boolean shouldMerge=false;


		Set<OWLIndividual> coreIndividuals_1 = s_1.getCore().getIndividual();

		Set<OWLIndividual> coreIndividuals_2= s_2.getCore().getIndividual();
		OWLIndividual  arbInd_1=coreIndividuals_1.iterator().next();
		OWLIndividual arbInd_2=coreIndividuals_2.iterator().next();

		SetMultimap<OWLIndividual, OWLIndividual> sameIndAssers=data.getABox().getSameIndAssers();
		//check if the equality assertion does not exist in the abox
		if(sameIndAssers.containsEntry(arbInd_1, arbInd_2)&&!isMergeContained(s_1, s_2)) {
			

			shouldMerge=true;


		}
		for(Linkey lk:data.getLKBox().getLks()) {
			if(strongSatisfaction(s_1, s_2, lk, mf)&&!isMergeContained(s_1, s_2)) {
				shouldMerge=true;
			}
		}

		return shouldMerge;
	}
	public boolean isMergeContained(Startype s_1,  Startype s_2) {
		for(Startype s:s_1.getAddress().getSstar()) {
			//R-neighbourhood relation
			if(s.getCore().getIndividual().containsAll(s_1.getCore().getIndividual())&&s.getCore().getIndividual().containsAll(s_2.getCore().getIndividual())&&s.getCore().getConcepts().containsAll(s_1.getCore().getConcepts())&&s.getCore().getConcepts().containsAll(s_2.getCore().getConcepts())) {
		//System.out.println("merge contained");
				return true;
			}
		}
		return false;
		
	}


	public Set<Startype> merge(Startype s_1,  Startype s_2,  ReasoningData data) {
		Set<Startype> merges=new HashSet<>();
		Startype merge1=new Startype();
		Startype merge2=new Startype();
		List<Triple> triples_1=s_1.getTriples(), triples_2=s_2.getTriples();

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
		return merges;
	}
	/*public void LkSaturation(Layer l, ReasoningData rd,  MatchingFn mf) {
		LinkkeyRules lkr=new LinkkeyRules();
		for(Linkey lk:rd.getLKBox().getLks()) {
			for(PropertyPair pp:lk.getPropertySet())
				for(Startype s_1:l.getSstar()) {
					for(Startype s_2:l.getSstar())
						if(!s_1.equals(s_2)) {
							lkr.chlk_1Rule(s_1, s_2, rd, lk, mf);
							lkr.chlk_2Rule(s_1, s_2, rd, lk, mf);

							lkr.lkRule(s_1, s_2, rd, lk,mf);

							lkr.merge(s_1, s_2, rd);
						}
				}
		}

	}*/

	/*
	 *  Apply the union (\sqcup) rule to "concept" (that must be a \sqcup-concept) in the core of the startype.
	 *  Create a new backtracking point as new unsat startype with history
	 * "his" of "this" is not explicitly changed since "updateCore" updates automatically
	 */
public boolean isLkRuleApp(Startype s1, Startype s2, LKBox LK, MatchingFn mf, ReasoningData data){
	for(Linkey lk:LK.getLks()) {
		//System.out.println(weakSatisfaction(s1, s2, lk, mf)&&!strongSatisfaction(s1, s2, lk, mf));
		//System.out.println(shouldMerge(s1, s2, data, mf));
	if((weakSatisfaction(s1, s2, lk, mf)&&!strongSatisfaction(s1, s2, lk, mf))||shouldMerge(s1, s2, data, mf)) {
	//System.out.println("here");
		return true;
	}
	}
	return false;
}

	@Override
	public boolean isUnionApp(Set<OWLClassExpression> asDisjuncts, Set<OWLClassExpression> concepts) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isCoreValid(Set<OWLClassExpression> cl, ReasoningData data) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public ConceptLabel getCore() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Startype updateCore(Set<OWLClassExpression> freshes, ReasoningData data) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void updateCore(Set<OWLClassExpression> freshes, SetMultimap<Triple, Triple> his, ReasoningData data) {
		// TODO Auto-generated method stub

	}



}
