package fr.anonymous.reasoner;


import java.util.Set;

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



}
