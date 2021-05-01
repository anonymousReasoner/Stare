package fr.anonymous.reasoner;

/*
 * the concept component of a link key
 */
import org.semanticweb.owlapi.model.OWLClassExpression;

public class ConceptPair {
	private OWLClassExpression firstConcept;
	private OWLClassExpression secondConcept;
	public ConceptPair(OWLClassExpression class_1, OWLClassExpression class_2) {
		this.firstConcept = class_1;
		this.secondConcept = class_2;
		// TODO Auto-generated constructor stub
	}
	public ConceptPair() {
		// TODO Auto-generated constructor stub
	}
	public OWLClassExpression getFirstConcept() {
		return firstConcept;
	}
	public void setFirstConcept(OWLClassExpression firstConcept) {
		this.firstConcept = firstConcept;
	}
	public OWLClassExpression getSecondConcept() {
		return secondConcept;
	}
	public void setSecondConcept(OWLClassExpression secondConcept) {
		this.secondConcept = secondConcept;
	}
	

}
