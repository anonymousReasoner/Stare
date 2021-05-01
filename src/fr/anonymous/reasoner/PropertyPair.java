package fr.anonymous.reasoner;

/*
 * the property component of a link key
 */
import org.semanticweb.owlapi.model.OWLPropertyExpression;

public class PropertyPair {

	private OWLPropertyExpression firstProperty;
	private OWLPropertyExpression secondProperty;
	public PropertyPair() {
		
	}
	public PropertyPair(OWLPropertyExpression firstProperty, OWLPropertyExpression secondProperty) {
		//super();
		this.firstProperty = firstProperty;
		this.secondProperty = secondProperty;
	}
	public OWLPropertyExpression getFirstProperty() {
		return firstProperty;
	}
	public void setFirstProperty(OWLPropertyExpression firstProperty) {
		this.firstProperty = firstProperty;
	}
	public OWLPropertyExpression getSecondProperty() {
		return secondProperty;
	}
	public void setSecondProperty(OWLPropertyExpression secondProperty) {
		this.secondProperty = secondProperty;
	}
	

}
