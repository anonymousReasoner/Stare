package fr.anonymous.reasoner;

/**
 * 
 */


import java.util.Set;

import org.semanticweb.owlapi.model.OWLClassExpression;

import com.google.common.collect.SetMultimap;

/**
 * @author kjradeh
 *
 */
public interface StartypeOperators {
	public boolean isUnionApp( Set<OWLClassExpression> asDisjuncts, Set<OWLClassExpression> concepts );
	 public boolean isCoreValid(Set<OWLClassExpression> cl, ReasoningData data);
	 public ConceptLabel getCore();
	 public Startype updateCore(Set<OWLClassExpression> freshes, ReasoningData data);
	  public void updateCore(Set<OWLClassExpression> freshes, SetMultimap<Triple, Triple> his, ReasoningData data);
	

}
