package fr.anonymous.reasoner;

import org.semanticweb.owlapi.model.OWLIndividual;

public class IndividualPair {
	OWLIndividual ind1;
	OWLIndividual ind2;
	public IndividualPair () {
	}
	public IndividualPair (OWLIndividual ind1, OWLIndividual ind2) {
		this.ind1=ind1;
		this.ind2=ind2;
		
	}
}
