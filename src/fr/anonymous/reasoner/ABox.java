package fr.anonymous.reasoner;


import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;
import com.google.common.collect.Sets;
import org.semanticweb.owlapi.model.*;
import java.io.Serializable;
import java.util.*;
import java.util.Map.Entry;

public class ABox implements Serializable {
    private static final long serialVersionUID = 1L;
    private Set<OWLIndividual> newInds;
    private List<OWLIndividual> initInds;//List indexes needed for BitSet
    private SetMultimap<OWLIndividual, OWLIndividual> sameIndAssers;//for both initInds and newinds
    private SetMultimap<OWLIndividual, OWLIndividual> diffIndAssers;
    private SetMultimap<OWLIndividual, OWLIndividual> closureByInd;

    //we need this own structure because there may be new individuals
    private SetMultimap<OWLIndividual, OWLClassExpression> conceptsByInd; //for both initInds and newinds
    private SetMultimap<OWLIndividual, Map<OWLObjectPropertyExpression, OWLIndividual>> conceptObjAssertsBySource;
    private SetMultimap<OWLIndividual, Map<OWLObjectPropertyExpression, OWLIndividual>> conceptObjAssertsByTarget;
    private SetMultimap<OWLIndividual, Map<OWLDataPropertyExpression, OWLLiteral>> conceptDataAssertsBySource;
    private SetMultimap<OWLLiteral, Map<OWLDataPropertyExpression, OWLIndividual>> conceptDataAssertsByTarget;
    public ABox() {
        initInds = new ArrayList<>();
        newInds = new HashSet<>();
        conceptsByInd = HashMultimap.create();
        conceptObjAssertsBySource = HashMultimap.create();
        conceptObjAssertsByTarget = HashMultimap.create();
        conceptDataAssertsBySource = HashMultimap.create();
        conceptDataAssertsByTarget = HashMultimap.create();
        sameIndAssers = HashMultimap.create();
        diffIndAssers = HashMultimap.create();
        closureByInd = HashMultimap.create();
    }
    // Generate sat, unsat startypes from initial individuals and form an Abox model
    public void init(ReasoningData data) {
        this.setTransitiveClosure();
    }

    /*
     * Merge x,y if x=y
     * This leads to update :
     *   1) L(x) <- L(x) + L(y)
     *   2) L(x,z) <- L(y,z)
     *   3) L(z,x) <- L(z,y)
     */
    /*
     * Two possible clashes : A, -A
     * x <> y : for each transitive closure x+, if x1, x2 belong to x+ and x1 <> x2 then there is a clash
     */
    // we don't deal with ABox clashes but with star-type clashes
    public boolean isClash(ReasoningData data) {
        // A, -A
        // check the classes of all individuals(
        for (OWLIndividual ind : conceptsByInd.keySet()) {
            if (!Startype.isCoreValid(conceptsByInd.get(ind), conceptsByInd.get(ind), data))
                return true;
        }

        for (Entry<OWLIndividual, OWLIndividual> entry : diffIndAssers.entries()) {
            if (closureByInd.containsKey(entry.getKey()) && closureByInd.containsValue(entry.getValue()) ||
                    closureByInd.containsValue(entry.getKey()) && closureByInd.containsKey(entry.getValue()))
                return true;
        }
        return false;
    }

    /*
     *  Updates the transitive closure of each individual occurring in sameIndAssers
     */
    public void setTransitiveClosure() {

        for (OWLIndividual entry : initInds) {
            closureByInd.put(entry, entry);
        }
        boolean saturated = false;
        while (!saturated) {
            saturated = true;
            for (Entry<OWLIndividual, OWLIndividual> entry : sameIndAssers.entries()) {
                for (OWLIndividual i : closureByInd.keySet()) {
                    if (closureByInd.get(i).contains(entry.getKey()) && !closureByInd.get(i).contains(entry.getValue())) {
                        closureByInd.put(i, entry.getValue());
                        saturated = false;
                    }
                    if (closureByInd.get(i).contains(entry.getValue()) && !closureByInd.get(i).contains(entry.getKey())) {
                        closureByInd.put(i, entry.getKey());
                        saturated = false;
                    }
                }
            }
        }
    }

    public SetMultimap<OWLIndividual, OWLIndividual> getClosureByInd() {
        return closureByInd;
    }

    public void addConceptAssertions() {
    }

    public void addIndividuals(List<OWLIndividual> ind) {
        this.initInds = ind;
    }

    public void addObjectPropertyAssertions() {
    }

    public void addDataPropertyAssertions() {
        // This will be used later in the presence of Data Properties
    }

    public SetMultimap<OWLIndividual, OWLClassExpression> getConceptsByInd() {
        return conceptsByInd;
    }

    public SetMultimap<OWLIndividual, Map<OWLObjectPropertyExpression, OWLIndividual>> getConceptObjeAssertBySource() {
        return conceptObjAssertsBySource;
    }

    public SetMultimap<OWLIndividual, Map<OWLObjectPropertyExpression, OWLIndividual>> getConceptObjeAssertByTarget() {
        return conceptObjAssertsByTarget;
    }


    public SetMultimap<OWLIndividual, Map<OWLDataPropertyExpression, OWLLiteral>> getConceptDataAssertBySource() {
        return conceptDataAssertsBySource;
    }

    public SetMultimap<OWLLiteral, Map<OWLDataPropertyExpression, OWLIndividual>> getConceptDataAssertByTarget() {
        return conceptDataAssertsByTarget;
    }

    public List<OWLIndividual> getInitInds() {
        return initInds;
    }

    public Set<OWLIndividual> getInds() {
        return Sets.union(new HashSet<OWLIndividual>(initInds), newInds);
    }

    public Set<OWLIndividual> getNewInds() {
        return newInds;
    }

    public SetMultimap<OWLIndividual, OWLIndividual> getSameIndAssers() {
        return sameIndAssers;
    }

    public SetMultimap<OWLIndividual, OWLIndividual> getDiffIndAssers() {
        return diffIndAssers;
    }

    public void setNewInds(Set<OWLIndividual> is) {
        newInds = is;
    }

    public void setInitInds(List<OWLIndividual> is) {
        initInds = is;
    }


    public void setSameIndAssers(SetMultimap<OWLIndividual, OWLIndividual> sameIndAssers) {
        this.sameIndAssers = sameIndAssers;
    }


    public SetMultimap<OWLIndividual, Map<OWLObjectPropertyExpression, OWLIndividual>> getConceptObjAssertsBySource() {
        return conceptObjAssertsBySource;
    }


    public void setConceptObjAssertsBySource(
            SetMultimap<OWLIndividual, Map<OWLObjectPropertyExpression, OWLIndividual>> conceptObjAssertsBySource) {
        this.conceptObjAssertsBySource = conceptObjAssertsBySource;
    }

    public void setConceptObjAssertsByTarget(
            SetMultimap<OWLIndividual, Map<OWLObjectPropertyExpression, OWLIndividual>> conceptObjAssertsByTarget) {
        this.conceptObjAssertsByTarget = conceptObjAssertsByTarget;
    }


    public void setConceptDataAssertsBySource(
            SetMultimap<OWLIndividual, Map<OWLDataPropertyExpression, OWLLiteral>> conceptDataAssertsBySource) {
        this.conceptDataAssertsBySource = conceptDataAssertsBySource;
    }


    public void setConceptDataAssertsByTarget(
            SetMultimap<OWLLiteral, Map<OWLDataPropertyExpression, OWLIndividual>> conceptDataAssertsByTarget) {
        this.conceptDataAssertsByTarget = conceptDataAssertsByTarget;
    }


    public void setDiffIndAssers(SetMultimap<OWLIndividual, OWLIndividual> diffIndAssers) {
        this.diffIndAssers = diffIndAssers;
    }


    public void setClosureByInd(SetMultimap<OWLIndividual, OWLIndividual> closureByInd) {
        this.closureByInd = closureByInd;
    }


    public void setConceptsByInd(SetMultimap<OWLIndividual, OWLClassExpression> conceptsByInd) {
        this.conceptsByInd = conceptsByInd;
    }

}
