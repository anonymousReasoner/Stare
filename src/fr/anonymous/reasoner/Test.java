package fr.anonymous.reasoner;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;

	/** Author: Matthew Horridge<br>
	 * The University Of Manchester<br>
	 * Bio-Health Informatics Group<br>
	 * Date: 11-Jan-2007 */
	
	public class Test {
	    private static final String PIZZA_IRI = "http://www.co-ode.org/ontologies/pizza/pizza.owl";

	    /** The examples here show how to load ontologies
	     * 
	     * @throws OWLOntologyCreationException */
	    public void shouldLoad() {
	        // Get hold of an ontology manager
	        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
	        // Let's load an ontology from the web
	        IRI iri = IRI.create("http://www.co-ode.org/ontologies/pizza/pizza.owl");
	        OWLOntology pizzaOntology=null;
			try {
				pizzaOntology = manager.loadOntologyFromOntologyDocument(iri);
			} catch (OWLOntologyCreationException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
	        System.out.println("Loaded ontology: " + pizzaOntology);
	    }
	        // Remove the ontology so that we can load a local cop
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		Test t= new Test();
		t.shouldLoad();

	}

}
