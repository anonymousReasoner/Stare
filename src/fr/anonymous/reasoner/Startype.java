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


import java.io.PrintWriter;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Vector;
import java.util.concurrent.CopyOnWriteArrayList;

import org.semanticweb.owlapi.model.*;
import com.google.common.collect.BiMap;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;
import com.google.common.collect.Sets;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;

public class Startype implements Serializable {
    private static final long serialVersionUhashcode = 1L;
    //for display/propagation
    private int idS = 0;
    //public static int nextIdS=1;
	/*public  int getNextIdS() {
		return this.nextIdS;
	}

	public  void setNextIdS(int nextIdS) {
		nextIdS = this.nextIdS;
	}*/

    //private static final int hashcode = 1;
    //This hashCode is not immutable. Therefore, each object should not be changed if it is hashed in a structure
    private int hashcode = 0;
    private static OWLDataFactory factory = new OWLDataFactoryImpl();
    private ConceptLabel core;
    private Set<OWLClassExpression> fresh;
    private Set<OWLClassExpression> processed;
    private Set<OWLClassExpression> allmax;

 /* public boolean isFirst() {
	return first;
}

public void setFirst(boolean first) {
	this.first = first;
}

public boolean isSecond() {
	return second;
}

public void setSecond(boolean second) {
	this.second = second;
}*/

    //The list of triples is not hashtable since each triple may be shared and modified arbitrarily
    //The number of triples is not large because the nb of existential concepts is not great
    //and the number in numbering restrictions is not great
    private List<Triple> triples;
    //If a non nominal startype has one triple,  it must be predecessor triple
    //A nominal startype may have several predecessors and successors.
    private List<Triple> predTriples;
    //isNominal == true if core.isNominal() returns true.
    private boolean isSaturated = false;
    private boolean isNominal = false;//
    //if this startype contains a clash, isValid=false,
    //if it is saturated and contains no clash, isValid=true
    //if it is unknown (being processed), isValid = null
    private Boolean isValid = null;
    private StartypePair parents = null;
    private Startype parent = null;
    private Layer address;

    public Startype getParent() {
        return parent;
    }

    public void setParent(Startype parent) {
        this.parent = parent;
    }

    public StartypePair getParents() {
        return parents;
    }

    public void setParents(StartypePair parents) {
        this.parents = parents;
    }

    public Startype() {


        this.isNominal = false;
        this.isSaturated = false;
        this.core = new ConceptLabel();
        //CopyOnWriteArrayList : thread-safe
        this.predTriples = new ArrayList<Triple>();//new CopyOnWriteArrayList<Triple>();
        this.triples = new ArrayList<Triple>();//new CopyOnWriteArrayList<Triple>();
        this.fresh = new HashSet<OWLClassExpression>();
        this.processed = new HashSet<OWLClassExpression>();
        this.allmax = new HashSet<OWLClassExpression>();
        hashcode = this.sumCode();
    }

    public Startype(ConceptLabel cl, ReasoningData data) {

        this.isNominal = false;
        this.isSaturated = false;
        this.core = new ConceptLabel(cl);
        this.fresh = new HashSet<OWLClassExpression>();
        this.processed = new HashSet<OWLClassExpression>();
        this.allmax = new HashSet<OWLClassExpression>();
        this.addFreshCore(cl.getConcepts(), data);
        this.triples = new ArrayList<Triple>();//new CopyOnWriteArrayList<Triple>();

        this.predTriples = new ArrayList<Triple>();//new CopyOnWriteArrayList<Triple>();
        if (this.core.isNominal())
            this.isNominal = true;
        hashcode = this.sumCode();
    }

    public Startype(ConceptLabel cl, Triple tr, ReasoningData data) {

        this.isNominal = false;
        this.isSaturated = false;
        this.core = new ConceptLabel(cl);
        this.fresh = new HashSet<OWLClassExpression>();
        this.processed = new HashSet<OWLClassExpression>();
        this.allmax = new HashSet<OWLClassExpression>();
        this.addFreshCore(cl.getConcepts(), data);
        this.triples = new ArrayList<Triple>();//new CopyOnWriteArrayList<Triple>();
        this.predTriples = new ArrayList<Triple>();//new CopyOnWriteArrayList<Triple>();
        this.addTripleToList(new Triple(this.getCore(), tr.getRay()).setCore(this.getCore()),
                this.isNominal() || !tr.getRay().getTip().isNominal());
        if (this.core.isNominal())
            this.isNominal = true;
        hashcode = this.sumCode();
    }

    //It includes "tr" and shares the core of "tr"
    public Startype(Triple tr, ReasoningData data) {


        this.isNominal = false;
        this.isSaturated = false;
        this.core = tr.getCore();
        this.predTriples = new ArrayList<Triple>();//new CopyOnWriteArrayList<Triple>();
        this.fresh = new HashSet<OWLClassExpression>();
        this.processed = new HashSet<OWLClassExpression>();
        this.allmax = new HashSet<OWLClassExpression>();
        this.addFreshCore(tr.getCore().getConcepts(), data);
        this.triples = new ArrayList<Triple>();//new CopyOnWriteArrayList<Triple>();
        this.triples.add(tr);
        if (this.core.isNominal())
            this.isNominal = true;
        //if(!this.isNominal() || !tr.getRay().getTip().getIndividuals().isEmpty())//bugged
        this.getPredTriples().add(tr);
        hashcode = this.sumCode();
    }

    // Create an exact copy of a startype "st" with cache
    // The core of all triples and the core of st are shared
    public Startype(Startype st) {

        this.core = new ConceptLabel(st.getCore());
        this.predTriples = new ArrayList<Triple>();//new CopyOnWriteArrayList<Triple>();
        this.fresh = new HashSet<OWLClassExpression>(st.getFreshCore());
        this.processed = new HashSet<OWLClassExpression>(st.getProcessedCore());
        this.allmax = new HashSet<OWLClassExpression>(st.getAllMaxCore());
        this.triples = new ArrayList<Triple>();//new CopyOnWriteArrayList<Triple>();
        for (Triple i : st.getTriples()) {
            this.addTripleToList(new Triple(i).setCore(this.getCore()), st.isPredTriple(i));
        }
        this.setNominal(st.isNominal());
        //"setValid" copies the value
        this.setValid(st.isValid());
        this.setSaturated(st.isSaturated());
        hashcode = this.sumCode();
    }
	/*
	 * Creates a startype (q, q') from st1=(p1, q), st2=(p2, q')  where st1 and st2 are saturated

  public Startype(Set<Triple> predTr, boolean nominal, Set<Triple> trs1, Set<Triple> trs2, Startype st1, Startype st2)
  {
	this.core = new ConceptLabel(st1.getCore());
	this.predTriples = new CopyOnWriteArrayList<Triple>();
	this.fresh = new HashSet<OWLClassExpression>( Sets.union(st1.getFreshCore(), st2.getFreshCore()) );
	this.processed = new HashSet<OWLClassExpression>( Sets.union( st1.getProcessedCore(), st2.getProcessedCore()) );
	this.allmax = new HashSet<OWLClassExpression>( Sets.union(st1.getAllMaxCore(), st2.getAllMaxCore() ));
	this.triples = new CopyOnWriteArrayList<Triple>();
	for(Triple i : trs1 )
	{
	  this.triples.add(new Triple(i).setCore(this.getCore()));
	}
	for(Triple i : trs2 )
	{
	  this.triples.add(new Triple(i).setCore(this.getCore()));
	}
	//Check when using !
	for(Triple i : predTr)
	{
	  this.addPredTriple(new Triple(i).setCore(this.getCore()));
    }
	this.setNominal( st1.isNominal() && st2.isNominal());
	if( st1.isValid()!=null && st1.isValid() && st2.isValid()!=null && st2.isValid() )
	   this.setValid( new Boolean(true) );
	this.setSaturated( st1.isSaturated() && st2.isSaturated() );
	updateHashCode();
  }*/

    // Create an exact copy of a startype "st" with cache
    // The core of all triples and the core of st are shared
    // Each element of "his" : newTr-oldTr
    // "his" must share the triples with the current startype and must not share the triples of the old startype
    public Startype(Startype st, SetMultimap<Triple, Triple> his) {


        this.core = new ConceptLabel(st.getCore());
        this.predTriples = new ArrayList<Triple>();//new CopyOnWriteArrayList<Triple>();
        this.fresh = new HashSet<OWLClassExpression>(st.getFreshCore());
        this.processed = new HashSet<OWLClassExpression>(st.getProcessedCore());
        this.allmax = new HashSet<OWLClassExpression>(st.getAllMaxCore());
        this.triples = new ArrayList<Triple>();//new CopyOnWriteArrayList<Triple>();
        for (Triple i : st.getTriples()) {
            this.addTripleWithHis(new Triple(i).setCore(this.getCore()), i, st.isPredTriple(i), his);
        }
        this.setNominal(st.isNominal());
        //"setValid" copies the value
        this.setValid(st.isValid());
        this.setSaturated(st.isSaturated());
        hashcode = sumCode();
    }

    /*
     * "newHis" must share the triples of the result "this"
     */
    public Startype(Startype st, SetMultimap<Triple, Triple> his, SetMultimap<Triple, Triple> newHis) {

        this.core = new ConceptLabel(st.getCore());
        this.predTriples = new ArrayList<Triple>();
        this.fresh = new HashSet<OWLClassExpression>(st.getFreshCore());
        this.processed = new HashSet<OWLClassExpression>(st.getProcessedCore());
        this.allmax = new HashSet<OWLClassExpression>(st.getAllMaxCore());
        this.triples = new ArrayList<Triple>();
        for (Triple i : st.getTriples()) {
            this.addTripleWithNewHis(new Triple(i).setCore(this.getCore()), i, st.isPredTriple(i), his, newHis);
        }
        this.setNominal(st.isNominal());
        this.setValid(st.isValid());
        this.setSaturated(st.isSaturated());
        hashcode = sumCode();
    }

    /************************************************************************************
     * Nouvelle construction SharedStartype(SetMultimap<Triple, Triple> his, SharedStartype st)
     */
    public Startype(SetMultimap<Triple, Triple> his, Startype st) {

        this.core = new ConceptLabel(st.getCore());
        this.predTriples = new CopyOnWriteArrayList<Triple>();
        this.fresh = new HashSet<OWLClassExpression>(st.getFreshCore());
        this.processed = new HashSet<OWLClassExpression>(st.getProcessedCore());
        this.allmax = new HashSet<OWLClassExpression>(st.getAllMaxCore());
        this.triples = new CopyOnWriteArrayList<Triple>();
        for (Triple i : st.getTriples()) {
            Triple newTr = new Triple(i);
            newTr.setCore(this.getCore());
            this.triples.add(newTr);
            if (st.getPredTriples().contains(i))
                this.getPredTriples().add(newTr);
            his.put(newTr, new Triple(i)); // j'ai chang  ici par rapport l'ancienne construction
        }
        this.setNominal(st.isNominal());
        this.setValid(st.isValid());
        this.setSaturated(st.isSaturated());
        hashcode = sumCode();
    }


    public ConceptLabel getCore() {
        return this.core;
    }

    /*
     *   It must update his since it is a hashtable
     */
    public Startype setCore(ConceptLabel id, SetMultimap<Triple, Triple> his, ReasoningData data) {
        this.addFreshCore(id.getConcepts(), data);
        SetMultimap<Triple, Triple> tmpHis = HashMultimap.create(his);
        this.core = id;
        his.clear();
        for (Triple tr : this.getTriples()) {
            Set<Triple> ss = tmpHis.get(tr);
            his.putAll(tr.setCore(id), ss);
        }
        this.setSaturated(false);
        this.setValid(null);
        if (!this.core.isNominal())
            this.isNominal = true;
        hashcode = sumCode();
        return this;
    }

    /*
     *   Its change triples as list not as a hashtable
     */
    public Startype setCore(ConceptLabel id, ReasoningData data) {
        this.addFreshCore(id.getConcepts(), data);
        this.core = id;
        for (Triple tr : this.getTriples()) {
            tr.setCore(id);
        }
        this.setSaturated(false);
        this.setValid(null);
        if (this.core.isNominal())
            this.isNominal = true;
        hashcode = sumCode();
        return this;
    }

    public Startype updateCore(Set<OWLClassExpression> freshes, ReasoningData data) {
        this.addFreshCore(freshes, data);
        //WE CHANGE CORE directly, and  all triples sharing the same core
        this.getCore().addAll(freshes);
        for (Triple tr : this.getTriples()) {
            tr.setCore(this.getCore());
        }
        this.setSaturated(false);
        this.setValid(null);
        if (this.core.isNominal())
            this.isNominal = true;
        hashcode = sumCode();
        return this;
    }

    /*
     * Updates core with "freshes"
     * It is supposed that the startype and triples are not hashed in any structure
     * Changes the triple objects
     * Updates his
     */
    public void updateCore(Set<OWLClassExpression> freshes, SetMultimap<Triple, Triple> his, ReasoningData data) {
        this.addFreshCore(freshes, data);
        this.getCore().addAll(freshes);
        SetMultimap<Triple, Triple> tmpHis = HashMultimap.create(his);
        his.clear();
        for (Triple tr : this.getTriples()) //each tr is changed
        {
            //System.out.println(tr.getCore().getConcepts());
            Set<Triple> ss = tmpHis.get(tr);
            his.putAll(tr.setCore(this.getCore()), ss);
        }
        this.setSaturated(false);
        this.setValid(null);
        if (this.core.isNominal())
            this.isNominal = true;
        hashcode = sumCode();
    }

    /*
     * Avoid using intermediate variables
     * His? history
     */
    public void addTripleWithHis(Triple tr, Triple ol, boolean pred, SetMultimap<Triple, Triple> his) {
        addTripleToList(tr, pred);
        his.put(tr, new Triple(ol));
    }

    public void addTripleWithNewHis(Triple tr, Triple ol, boolean pred, SetMultimap<Triple, Triple> his,
                                    SetMultimap<Triple, Triple> newHis) {
        addTripleToList(tr, pred);
        for (Triple t : his.get(ol)) {
            if (t == null)
                newHis.put(tr, null);
            else
                newHis.put(tr, new Triple(t));
        }
    }

    public void addTripleToList(Triple tr, boolean pred) {
        if (!this.getTriples().contains(tr))
            this.getTriples().add(tr);
        if (pred && !this.getPredTriples().contains(tr))
            this.getPredTriples().add(tr);
    }

    /*
     * "tr" must shares the core with "this". So "tr" can change
     *
     */
    public boolean addTriple(Triple tr) {
        if (this.getTriples().contains(tr))
            return false;
        tr.setCore(this.getCore());
        if ((this.getTriples().isEmpty() && !this.isNominal()) ||
                (tr.getRay().getTip().isNominal() && !this.getPredTriples().contains(tr)))
            this.getPredTriples().add(tr);
        this.getTriples().add(tr);
        this.setSaturated(false);
        this.setValid(null);
        hashcode = sumCode();
        return true;
    }

    public Startype addTriple(Triple tr, SetMultimap<Triple, Triple> his) {
        if (this.getTriples().contains(tr) || !tr.getCore().equals(this.getCore()))
            return this;
        //the core of all triples has the same address of the core of st
        tr.setCore(this.getCore());
        if ((this.getTriples().isEmpty() && !this.isNominal()) ||
                (tr.getRay().getTip().isNominal() && !this.getPredTriples().contains(tr)))
            this.getPredTriples().add(tr);
        this.getTriples().add(tr);
        his.put(tr, null);
        this.setSaturated(false);
        this.setValid(null);
        hashcode = sumCode();
        return this;
    }

    /* Adds a new triple with tip "freshes" and "role"
     This object st should not be hashed in any structure
     */
    public Startype addTriple(Set<OWLClassExpression> freshes, OWLPropertyExpression role, ReasoningData data) {
        Triple tr = new Triple(this.getCore(), new Ray(new RoleLabel(role, data), new ConceptLabel(freshes)));
        if (this.getTriples().contains(tr) || !tr.getCore().equals(this.getCore()))
            return this;
        //the new triple share the same core
        tr.setCore(this.getCore());
        if ((this.getTriples().isEmpty() && !this.isNominal()) ||
                (tr.getRay().getTip().isNominal()) && !this.getPredTriples().contains(tr))
            this.getPredTriples().add(tr);
        this.getTriples().add(tr);
        this.setSaturated(false);
        this.setValid(null);
        hashcode = sumCode();
        return this;
    }

    public Startype addTriple(Set<OWLClassExpression> freshes, OWLPropertyExpression role, SetMultimap<Triple, Triple> his, ReasoningData data) {
        Triple tr = new Triple(this.getCore(), new Ray(new RoleLabel(role, data), new ConceptLabel(freshes)));
        if (this.getTriples().contains(tr) || !tr.getCore().equals(this.getCore()))
            return this;
        // the new triple share the same core
        tr.setCore(this.getCore());
        if ((this.getTriples().isEmpty() && !this.isNominal()) || (tr.getRay().getTip().isNominal() && !this.getPredTriples().contains(tr)))
            this.getPredTriples().add(tr);
        this.getTriples().add(tr);
        his.put(tr, null);
        this.setSaturated(false);
        this.setValid(null);
        hashcode = sumCode();
        return this;
    }

    /*
     * This method changes hashCode of "this". The core of "nr" must be the core of this
     * Not needed to change Cache since nr > or (to check)
     */

    public Startype replaceTriple(Triple or, Triple nr) {
        if (!this.getTriples().contains(or) ||
                this.getTriples().contains(nr) ||
                !nr.getCore().equals(this.getCore()))
            return this;
        this.getTriples().remove(or);
        nr.setCore(this.getCore());
        if (this.getPredTriples().contains(or)) {
            this.getPredTriples().remove(or);
            this.getPredTriples().add(nr);
        }
        if (nr.getRay().getTip().isNominal() &&
                !this.getPredTriples().contains(nr))
            this.getPredTriples().add(nr);
        this.getTriples().add(nr);
        this.setSaturated(false);
        this.setValid(null);
        hashcode = sumCode();
        return this;
    }

    public Startype replaceTriple(Triple or, Triple nr, SetMultimap<Triple, Triple> his) {
        if (!this.getTriples().contains(or) || this.getTriples().contains(nr))
            return this;
        this.getTriples().remove(or);
        nr.setCore(this.getCore());
        if (this.getPredTriples().contains(or)) {
            this.getPredTriples().remove(or);
            this.getPredTriples().add(nr);
        }
        if (nr.getRay().getTip().isNominal() &&
                !this.getPredTriples().contains(nr))
            this.getPredTriples().add(nr);
        this.getTriples().add(nr);
        Set<Triple> ss = new HashSet<Triple>(his.get(or));//bugged without new due to removeAll(or)
        his.removeAll(or);
        his.putAll(nr, ss);
        this.setSaturated(false);
        this.setValid(null);
        hashcode = sumCode();
        return this;
    }

    /*
     *  Replace old one by the new one. "freshes" is added to the tip of the triple
     *  Cache does not need to change because the "tip" augments
     */
    public Startype updateTriple(Vector<Triple> trVector, Set<OWLClassExpression> freshes, ReasoningData data) {
        this.replaceTriple(trVector.get(0),
                new Triple(this.getCore(),
                        new Ray(trVector.get(0).getRay().getRidge(),
                                trVector.get(0).getRay().getTip().getNewConceptLabel(freshes))));
        this.setSaturated(false);
        this.setValid(null);
        hashcode = sumCode();
        return this;
    }

    public Startype updateTriple(Triple tr, Set<OWLClassExpression> freshes, SetMultimap<Triple, Triple> his, ReasoningData data) {
        this.replaceTriple(tr,
                new Triple(this.getCore(),
                        new Ray(tr.getRay().getRidge(),
                                tr.getRay().getTip().getNewConceptLabel(freshes))), his);
        this.setSaturated(false);
        this.setValid(null);
        hashcode = sumCode();
        return this;
    }

    /*
     *  Merges two triples into a new triple and replace them with the new one
     */
    public Startype mergeTriples(Triple triple1, Triple triple2, ReasoningData data) {
        Triple tr = new Triple(this.getCore(),
                new Ray(triple1.getRay().getRidge().getNewRoleLabel(triple2.getRay().getRidge().getRoles(), data),
                        triple1.getRay().getTip().getNewConceptLabel(triple2.getRay().getTip().getConcepts())));
        this.getTriples().remove(triple1);
        this.getTriples().remove(triple2);
        tr.setCore(this.getCore());
        if (!this.getTriples().contains(tr)) {
            if (this.getPredTriples().contains(triple1) || this.getPredTriples().contains(triple2)) {
                this.getPredTriples().remove(triple1);
                this.getPredTriples().remove(triple2); //if triple_1 is not predecessor it works
                this.getPredTriples().add(tr);
            }
            this.getTriples().add(tr);
        }
        this.setSaturated(false);
        this.setValid(null);
        hashcode = sumCode();
        return this;
    }

    /*
     *  Merges two triples into a new triple, replaces them with the new one and updates the keys of "his" (the values of his are not changed)
     *  It is impossible that newTriple equals an existing triple since (newLabelConcept_i, newLabelConcept_j) appears once in triple tips
     *
     *  his(triple) is null if triple is fresh by generating
     *  before saturating, values of "his" are never null
     *  his(triple) may have different values caused by merging
     *
     *  So, his(newTriple) = his(triple1) \/ his(triple2)  and removing multiple null (null by generating is not needed to be stored after merging)
     *  since, if his(triple1) = null and  his(triple1) = null then his(newTriple) = null (both are fresh)
     *         if his(triple1) <> null and his(triple2) = null  then his(newTriple) = his(triple1)
     *         if his(triple1) <> null and his(triple2) <> null  then his(newTriple) = his(triple1) \/ his(triple2)
     */
    public Startype mergeTriples(Triple triple1, Triple triple2, SetMultimap<Triple, Triple> his, ReasoningData data) {
        boolean pred = false;
        boolean freshTriple = false;
        if (this.isPredTriple(triple1) || this.isPredTriple(triple2))
            pred = true;
        Triple newTr = new Triple(this.getCore(),
                new Ray(triple1.getRay().getRidge().getNewRoleLabel(triple2.getRay().getRidge().getRoles(), data),
                        triple1.getRay().getTip().getNewConceptLabel(triple2.getRay().getTip().getConcepts()))); //creates a new triple into which triple1, triple2 are merged
        this.getTriples().remove(triple1);
        this.getTriples().remove(triple2);
        Set<Triple> vs1 = new HashSet<Triple>(his.get(triple1)); //vs1, vs2 may contain null and are never empty
        Set<Triple> vs2 = new HashSet<Triple>(his.get(triple2));
        if (vs1.contains(null) && vs2.contains(null))
            freshTriple = true;
        his.removeAll(triple1);
        his.removeAll(triple2);
        newTr.setCore(this.getCore());
        if (!this.getTriples().contains(newTr))  //the opposite is not possible!
        {
            this.getTriples().add(newTr); //adding new triple after removing two triples
            if (freshTriple) //both triple1 and triple2 are fresh
                his.put(newTr, null);
            else {
                vs1.addAll(vs2);
                vs1.remove(null);
                his.putAll(newTr, vs1);
            }
            if (pred) {
                this.getPredTriples().clear();
                this.getPredTriples().add(newTr);
            }
        }
        this.setSaturated(false);
        this.setValid(null);
        hashcode = sumCode();
        return this;
    }

    /*
     *  Check whether this startype contains "st" by label of each triple
     */
    public boolean containsAll(Startype st) {
        for (Triple tr1 : st.getTriples()) {
            boolean included = false;
            for (Triple tr2 : this.getTriples()) {
                if (tr2.containsAll(tr1)) {
                    included = true;
                    break;
                }
            }
            if (!included)
                return false;
        }
        return true;
    }

    /*
     * When both  A and -A  are absorbed, it is needed to add A \cup -A
     */
    public void atomicNegatedRule(OWLClassExpression concept, SetMultimap<Triple, Triple> his, ReasoningData data) {
        Set<OWLClassExpression> freshes = new HashSet<OWLClassExpression>();
        freshes.add(factory.getOWLObjectUnionOf(concept, factory.getOWLObjectComplementOf(concept).getNNF()));
        this.updateCore(freshes, his, data);
    }

    public boolean isAtomicNegatedRule(OWLClassExpression concept, SetMultimap<Triple, Triple> his, ReasoningData data) {
        if (this.getCore().getConcepts().contains(concept))
            return true;
        if (this.getCore().getConcepts().contains(factory.getOWLObjectComplementOf(concept).getNNF()))
            return true;
        if (this.getCore().getConcepts().contains(factory.getOWLObjectUnionOf(concept, factory.getOWLObjectComplementOf(concept).getNNF())))
            return true;
        else
            return false;
    }


    /* Applies the intersection (\sqcap) rule to "concept" (that must be a \scap-concept) in the core of the startype
     * The application of rule may add fresh concept to cache and update the startype (with updateCore)
     * "his" is updated automatically because "newTriple" belong to "this"
     * It return true if this changes
     *
     */
    public Startype intersectionRule(Startype st_input, OWLClassExpression concept, SetMultimap<Triple, Triple> his, ReasoningData data) {
        Startype st = new Startype();

        ConceptLabel cl = new ConceptLabel();
//LinkedHashSet<OWLClassExpression> c2=new LinkedHashSet<OWLClassExpression>();

        //  Set<OWLClassExpression> concepts = data.getConceptsFromPrimitiveAxioms(st_input.getCore().getConcepts(), new HashSet<OWLClassExpression>());
			/*cl.setConcepts(c2);
			ConceptLabel cl1=new ConceptLabel(concepts);
			cl1.setIndividual(star.getCore().getIndividual());*/

        cl.setConcepts(st_input.getCore().getConcepts());

        cl.setIndividual(st_input.getCore().getIndividual());
        st.setCore(cl, data);

        List<Triple> trs = st_input.getTriples();
        for (Triple tr : trs) {

            tr.setCore(cl);
        }
        st_input.setTriples(trs);

        //returns the conjuncted concepts
        Set<OWLClassExpression> freshes = new HashSet<OWLClassExpression>(concept.asConjunctSet());
        freshes.remove(data.getTop());
        freshes.addAll(data.getConceptsFromPrimitiveAxioms(freshes, st.getCore().getConcepts()));
        freshes.removeAll(st.getCore().getConcepts());
        freshes.remove(data.getTop());// If all conjunctions are top
        //the atomic concepts already exists

        if (freshes.isEmpty()) {
            return st;
        }
        // if the addition of atomic concepts does not affect the validity of a star-type
        if (!this.isCoreValid(freshes, data)) {
            //if( !this.isComplexValid(freshes, data) ) {
            this.updateCore(freshes, his, data);
            this.setValid(new Boolean(false));
            return null;
        }
        // I update the core but don't set the star-type valid
        this.updateCore(freshes, his, data);
        return st;
    }

    /*
     *  Return true if application of this rule must change "this"
     */
    public boolean isIntersectionRule(OWLClassExpression concept, ReasoningData data) {
        //System.out.println("concept: "+this.getCore().getConcepts());
        Set<OWLClassExpression> freshes = new HashSet<OWLClassExpression>(concept.asConjunctSet());
        //System.out.println("conjucts: "+concept.asConjunctSet());
        //System.out.println("inter: "+(concept instanceof OWLObjectIntersectionOf));
        if (this.getCore().getConcepts().containsAll(freshes)) {

            return false;
        } else {
            return true;
        }

	   /* freshes.addAll(data.getConceptsFromPrimitiveAxioms(freshes, this.getCore().getConcepts() ));
	  //  System.out.println( data.getConceptsFromPrimitiveAxioms(freshes, this.getCore().getConcepts() ));
	    freshes.removeAll(this.getCore().getConcepts());
	  //  System.out.println(freshes.contains(concept));
	    if( freshes.isEmpty() )
	    {
		  return false;
	    } else
	      return true;*/



		/*Set<OWLClassExpression> freshes = new HashSet<OWLClassExpression>(concept.asConjunctSet());

	/*
		System.out.println("for-all: "+(concept instanceof OWLObjectAllValuesFrom));
	System.out.println("Union: "+(concept instanceof OWLObjectUnionOf));
	System.out.println("Exist: "+(concept instanceof OWLObjectIntersectionOf));*/
	   /* freshes.remove(data.getTop());

	    freshes.addAll(data.getConceptsFromPrimitiveAxioms(freshes, this.getCore().getConcepts() ));

	    freshes.removeAll(this.getCore().getConcepts());



	    if( freshes.isEmpty() )
	    {
		  return false;
	    }
	    else
	      return true;*/
    }

    // (A or B or C) = (A or B) or C; {(A or B or C), (A or B), E, F} => no needed to apply UnionRule to (A or B or C)
    // check the need for applying the union app
    public boolean isUnionApp(Set<OWLClassExpression> asDisjuncts, Set<OWLClassExpression> concepts) {
        // the disjuncts already exists in the core
        if (!Sets.intersection(asDisjuncts, concepts).isEmpty())
            return false;
        return true;
    }

    public boolean checkHis(SetMultimap<Triple, Triple> his) {
        // check if a triple already exists in the star-type
        Set<Triple> ts = his.keySet();
        for (Triple s : ts)
            if (!ts.contains(s))
                return false;
        return true;
    }

    /*
     *  Apply the union (\sqcup) rule to "concept" (that must be a \sqcup-concept) in the core of the startype.
     *  Create a new backtracking point as new unsat startype with history
     * "his" of "this" is not explicitly changed since "updateCore" updates automatically
     */
    public void unionRule(OWLClassExpression concept, SetMultimap<Triple, Triple> his,
                          Map<Startype, SetMultimap<Triple, Triple>> hisByUnsat, ReasoningData data) {
        //ManchesterOWLSyntaxOWLObjectRendererImpl render = new ManchesterOWLSyntaxOWLObjectRendererImpl();

        Set<OWLClassExpression> operands = concept.asDisjunctSet();
        // supposed that each disjunction includes at least two distinct disjuncts (OWLClassExpression reduces)
        if (operands.size() == 1 || operands.contains(data.getTop())) {
            return;
        }
        //The disjunction shares a disjunct with the current core
        if (!isUnionApp(operands, this.getCore().getConcepts())) {
            return;
        }

        //Set<OWLClassExpression> freshesFirst = new HashSet<OWLClassExpression>();
        OWLClassExpression first = operands.iterator().next();
        operands.remove(first);

        // I should store the others in a new created startype, then I'll came back
        if (operands.size() > 1) {
            Set<OWLClassExpression> freshesRemain = new HashSet<OWLClassExpression>();
            freshesRemain.add(factory.getOWLObjectUnionOf(operands));
            if (this.isCoreValid(freshesRemain, data)) {
                SetMultimap<Triple, Triple> newHis = HashMultimap.create(50, 50);
                // creation of new startype
                Startype st = new Startype(this, his, newHis);
                st.updateCore(freshesRemain, newHis, data);

                //maybe different in our case, this is a backtracking point for this specific star-type, not directly added
                //to the layer
                hisByUnsat.put(st, newHis);
            }
        }
        //only one disjunct
        else {

            Set<OWLClassExpression> freshesRemain = operands.iterator().next().asConjunctSet();
            freshesRemain.addAll(data.getConceptsFromPrimitiveAxioms(freshesRemain, this.getCore().getConcepts()));
            freshesRemain.removeAll(this.getCore().getConcepts());
            freshesRemain.remove(data.getTop());
            if (freshesRemain.isEmpty())
                return;
            if (this.isCoreValid(freshesRemain, data)) {
                SetMultimap<Triple, Triple> newHis = HashMultimap.create();
                Startype st = new Startype(this, his, newHis);
                st.updateCore(freshesRemain, newHis, data);
                hisByUnsat.put(st, newHis);
            }
        }
        // In all cases
        Set<OWLClassExpression> freshesFirst = first.asConjunctSet();
        freshesFirst.addAll(data.getConceptsFromPrimitiveAxioms(freshesFirst, this.getCore().getConcepts()));
        freshesFirst.removeAll(this.getCore().getConcepts());
        freshesFirst.remove(data.getTop());
        if (freshesFirst.isEmpty()) {
            return;
        }

        if (this.isCoreValid(freshesFirst, data)) {
            this.updateCore(freshesFirst, his, data);
        } else {
            this.updateCore(freshesFirst, his, data); //his is not needed since invalid
            this.setValid(new Boolean(false));
        }
    }

    /*
     *  Apply the union (\sqcup) rule to "concept" (that must be a \sqcup-concept) in the core of the startype.
     *  Create a new backtracking point as new unsat startype with history
     * "his" of "this" is not explicitly changed since "updateCore" updates automatically
     */
    // correct the union rule and think about the concurrent exception
    public Set<Startype> unionRule_new(Startype star, OWLClassExpression concept, SetMultimap<Triple, Triple> his,
                                       ReasoningData data) {


        Set<Startype> choices = new HashSet<Startype>();

        //ManchesterOWLSyntaxOWLObjectRendererImpl render = new ManchesterOWLSyntaxOWLObjectRendererImpl();

        Set<OWLClassExpression> operands = concept.asDisjunctSet();
        //System.out.println(operands);

        LinkedHashSet<OWLClassExpression> c1 = star.getCore().getConcepts();

        for (OWLClassExpression c : operands) {

            Startype star_d = new Startype();
            ConceptLabel cl = new ConceptLabel();

            LinkedHashSet<OWLClassExpression> c2 = new LinkedHashSet<OWLClassExpression>();
            c2.addAll(c1);
            c2.add(c);
            Set<OWLClassExpression> concepts = data.getConceptsFromPrimitiveAxioms(c2, new HashSet<OWLClassExpression>());
            cl.setConcepts(c2);
            ConceptLabel cl1 = new ConceptLabel(concepts);
            cl1.setIndividual(star.getCore().getIndividual());
            star_d.setCore(cl1, data);
            List<Triple> trs = star.getTriples();
            for (Triple tr : trs) {

                tr.setCore(cl);
            }
            star_d.setTriples(trs);

            star_d.setNominal(star.isNominal());

            choices.add(star_d);


        }

        //System.out.println("The number of choices are:"+choices.size());
        return choices;

    }


    void setCore(ConceptLabel core2) {
        // TODO Auto-generated method stub

    }

    public boolean isUnionRule(OWLClassExpression concept, ReasoningData data) {


        Set<OWLClassExpression> operands = new HashSet<OWLClassExpression>(concept.asDisjunctSet());

        // supposed that each disjunction includes at least two distinct disjuncts (OWLClassExpression reduces)
        if (operands.size() == 1 || operands.contains(data.getTop())) {


            return false;
        }
        if (!isUnionApp(operands, this.getCore().getConcepts())) {
            return false;
        }
        // For each "oper", we compute all "freshes" from primitive axioms and remove those included already in the current core
        for (OWLClassExpression oper : operands) {

            Set<OWLClassExpression> freshes = new HashSet<OWLClassExpression>();
            freshes.addAll(data.getConceptsFromPrimitiveAxioms(oper.asConjunctSet(), this.getCore().getConcepts()));
            freshes.removeAll(this.getCore().getConcepts());
            if (freshes.isEmpty()) {
                return false;
            }
        }
        return true;
    }

    // Apply the some (\exists) rule to "concept" (that must be a \exists-concept) in the core of the startype.
    // hook is always a triple of the current st; bkTrack is used to store bkTr points by choice and max rules
    // When a ray is added, all, max rules are applied to the new one.
    public void someRule(OWLClassExpression concept, SetMultimap<Triple, Triple> his, ReasoningData data) {

        for (Triple triple : this.getTriples()) {
            //Return if the rule is not applicable
            if (triple.getRay().getTip().getConcepts().containsAll(((OWLObjectSomeValuesFrom) concept).getFiller().asConjunctSet())) {

                if (triple.getRay().getRidge().getRoles().contains(((OWLObjectSomeValuesFrom) concept).getProperty())) {
                    return;
                }
            }
        }
        Set<OWLClassExpression> tAug = data.getConceptsFromPrimitiveAxioms(
                Sets.union(((OWLObjectSomeValuesFrom) concept).getFiller().asConjunctSet(), data.getInitCore().getConcepts()),
                new HashSet<OWLClassExpression>());
        if (((OWLObjectSomeValuesFrom) concept).getFiller() instanceof OWLObjectOneOf) {
            tAug.addAll(data.getConceptsForIndividuals(((OWLObjectOneOf) ((OWLObjectSomeValuesFrom) concept).getFiller()).getIndividuals()));
        }
        // if not valid we exist
        if (!Startype.isCoreValid(tAug, new HashSet<OWLClassExpression>(), data)) //is it necessary ?
        //if( !this.isComplexValid(tAug, new HashSet<OWLClassExpression>(), data) )
        {
            this.setValid(new Boolean(false));
            return;
        }
        //finally this rule results in adding a triple
//	tAug is  the classes, property
        //  this.addTriple(tAug,((OWLObjectSomeValuesFrom)concept).getProperty(), his, data);
        this.addTriple(tAug, ((OWLObjectSomeValuesFrom) concept).getProperty(), data);
    }

    public Startype stsomeRule(Startype st, OWLClassExpression concept, SetMultimap<Triple, Triple> his, ReasoningData data, MatchingFn mf, CompressedTableau ct, OWLOntology ontology) {

        Startype copy_st = new Startype();
        copy_st.setCore(st.getCore());
        //copy_st.setTriples(st.get());
        ConceptLabel cl1 = new ConceptLabel();


        cl1.setConcepts(st.getCore().getConcepts());

        cl1.setIndividual(st.getCore().getIndividual());
        copy_st.setCore(cl1, data);
        List<Triple> trs = st.getTriples();
        for (Triple tr : trs) {

            tr.setCore(cl1);
        }
        copy_st.setTriples(trs);


        for (Triple t : copy_st.getTriples()) {
            Omega o = new Omega();
            //	System.out.println(t.getRay().getTip().getIndividual());
            o.setS(copy_st);
            o.setT(t);
            mf.getMatch().add(o);
        }


        if (concept instanceof OWLObjectSomeValuesFrom) {
            OWLObjectSomeValuesFrom res = (OWLObjectSomeValuesFrom) concept;
            Triple t = new Triple();
            RoleLabel rl = new RoleLabel();
            rl.add(((OWLObjectSomeValuesFrom) concept).getProperty());
            t.getRay().setRidge(rl);

            ConceptLabel cl = new ConceptLabel();
            t.setCore(cl);

            cl.setConcepts(st.getCore().getConcepts());


            LinkedHashSet<OWLClassExpression> cFiller = new LinkedHashSet<OWLClassExpression>();
            cFiller.add(((OWLObjectSomeValuesFrom) concept).getFiller());

            t.getRay().getTip().setConcepts(cFiller);

            copy_st.getTriples().add(t);
            if (copy_st.isCoreValid(copy_st.getCore().getConcepts(), data) && copy_st.isCoreValidInd(copy_st, ontology)) {

                mf.matchTriple(copy_st, t, this, null, this.getAddress(), ct, mf, data);
            }


        }

        copy_st.setNominal(this.isNominal());

        return copy_st;
    }

    public boolean isSomeRule(OWLClassExpression concept, ReasoningData data, Layer l, CompressedTableau ct) {
        boolean isSome = false;
        if (!l.isBlocked(this, ct, l)) {

            if (concept instanceof OWLObjectSomeValuesFrom) {

                //factory.getOWLObjectSomeValuesFrom();
                OWLObjectSomeValuesFrom res = (OWLObjectSomeValuesFrom) concept;
                if (this.getTriples().size() == 0) {

                    isSome = true;
                } else {

                    for (Triple triple : this.getTriples()) {


                        if (triple.getRay().getRidge().getRoles().contains(res.getProperty()) && triple.getRay().getTip().getConcepts().contains(res.getFiller())) {

                            isSome = false;
                        } else {
                            isSome = true;
                        }

                    }
                }
            }
        }


        return isSome;

    }

    public boolean checkForMinTriples(OWLPropertyExpression role, OWLClassExpression concept, int N, ReasoningData data) {
        int c = 0;
        for (Triple tr : this.getTriples()) {
            if ((tr.getRay().getTip().getConcepts().contains(concept) || concept.equals(data.getTop())) &&
                    tr.getRay().getRidge().getRoles().contains(role)) {
                c++;
                if (c >= N) return true;
            }
        }
        return false;
    }

    //not for ALC
    public void minRule(OWLClassExpression concept, SetMultimap<Triple, Triple> his, ReasoningData data) {
        //OWLPropertyExpression role = ((OWLObjectMinCardinality)concept).getProperty();
        //OWLClassExpression filler = ((OWLObjectMinCardinality)concept).getFiller();
        //int card =  ((OWLObjectMinCardinality)concept).getCardinality();
        // Return if it is not necessary to add neighbors
        if (checkForMinTriples(((OWLObjectMinCardinality) concept).getProperty(),
                ((OWLObjectMinCardinality) concept).getFiller(), ((OWLObjectMinCardinality) concept).getCardinality(), data)) {
            return;
        }

        //Set<OWLClassExpression> tipC =  new HashSet<OWLClassExpression>(filler.asConjunctSet());
        //if( !filler.equals(data.getTop()))
        //    tipC.add(filler);
        //Set<OWLClassExpression> tipC =  new HashSet<OWLClassExpression>(Collections.singleton(filler) );
        //tipC.addAll( data.getInitCore().getConcepts() );

        Set<OWLClassExpression> tAug = data.getConceptsFromPrimitiveAxioms(
                Sets.union(((OWLObjectMinCardinality) concept).getFiller().asConjunctSet(), data.getInitCore().getConcepts()),
                new HashSet<OWLClassExpression>());
        //use data.getConceptsForIndividuals if nominals
        if (!Startype.isCoreValid(tAug, new HashSet<OWLClassExpression>(), data)) //is it necessary ?
        //if( !this.isComplexValid(tAug, new HashSet<OWLClassExpression>(), data) )
        {
            this.setValid(new Boolean(false));
            return;
        }
        List<OWLClass> names = data.getMinNames(concept);
        for (int i = 0; i < ((OWLObjectMinCardinality) concept).getCardinality(); i++) {
            Set<OWLClassExpression> tmp = new HashSet<OWLClassExpression>(tAug);
            tmp.add(names.get(i));
            this.addTriple(tmp, ((OWLObjectMinCardinality) concept).getProperty(), his, data);
        }
    }

    //not for ALC
    public boolean isMinRule(OWLClassExpression concept, ReasoningData data) {
        //OWLPropertyExpression role = ((OWLObjectMinCardinality)concept).getProperty();
        //OWLClassExpression filler = ((OWLObjectMinCardinality)concept).getFiller();
        //int card =  ((OWLObjectMinCardinality)concept).getCardinality();
        // Return if it is not necessary to add neighbors
        if (checkForMinTriples(((OWLObjectMinCardinality) concept).getProperty(), ((OWLObjectMinCardinality) concept).getFiller(),
                ((OWLObjectMinCardinality) concept).getCardinality(), data)) {
            return false;
        } else
            return true;
    }

    // /forall rule
    public boolean allRule(OWLClassExpression concept, SetMultimap<Triple, Triple> his, ReasoningData data) {
        //OWLPropertyExpression role = ((OWLObjectAllValuesFrom)concept).getProperty();
        //OWLClassExpression filler = ((OWLObjectAllValuesFrom)concept).getFiller();
        //ManchesterOWLSyntaxOWLObjectRendererImpl render = new ManchesterOWLSyntaxOWLObjectRendererImpl();
        //Some triples may ne replaced with updated ones
        //Gets the value which is the filler for this restriction.

        boolean changed = false;

        //Traverse through the same triple objects but other set
        for (Triple triple : new CopyOnWriteArrayList<Triple>(this.getTriples()))//as a list an element can be changed
        {


            if (triple.getRay().getRidge().getRoles().contains(((OWLObjectAllValuesFrom) concept).getProperty())) {
                if (triple.getRay().getTip().getConcepts().containsAll(((OWLObjectAllValuesFrom) concept).getFiller().asConjunctSet())) {
                    continue;
                    //return;//because this triple is fresh and does not contains filler!
                } else {
                    Set<OWLClassExpression> tAug = data.getConceptsFromPrimitiveAxioms(
                            Sets.union(((OWLObjectAllValuesFrom) concept).getFiller().asConjunctSet(), data.getInitCore().getConcepts()),
                            triple.getRay().getTip().getConcepts());
                    //use data.getConceptsForIndividuals if nominals
                    if (!Startype.isCoreValid(tAug, triple.getRay().getTip().getConcepts(), data)) //is it necessary ?
                    //if( !this.isComplexValid(tAug, triple.getRay().getTip().getConcepts(), data) )
                    {
                        this.setValid(new Boolean(false));
                        return true;
                    }
                    //The triple in vect is a copy of that triple in the startype
                    //this.updateTriple(new Vector<Triple>(Collections.singleton(triple)), tAug, his,  data);
                    this.updateTriple(triple, tAug, his, data);
                    changed = true;
                }
            }
        }
        return changed;
    }

    public Startype stAllRule(OWLClassExpression concept, SetMultimap<Triple, Triple> his, ReasoningData data, MatchingFn mf, CompressedTableau ct, OWLOntology ontology) {

        //OWLPropertyExpression role = ((OWLObjectAllValuesFrom)concept).getProperty();
        //OWLClassExpression filler = ((OWLObjectAllValuesFrom)concept).getFiller();
        //ManchesterOWLSyntaxOWLObjectRendererImpl render = new ManchesterOWLSyntaxOWLObjectRendererImpl();
        //Some triples may ne replaced with updated ones
        //Gets the value which is the filler for this restriction.
        Startype st_copy = new Startype();


        ConceptLabel cl = new ConceptLabel();
//LinkedHashSet<OWLClassExpression> c2=new LinkedHashSet<OWLClassExpression>();


        cl.setConcepts(this.getCore().getConcepts());

        cl.setIndividual(this.getCore().getIndividual());

        List<Triple> trs = this.getTriples();
        st_copy.setCore(cl, data);
        //st_copy.setTriples(trs);


        boolean changed = false;
        //Traverse through the same triple objects but other set
        OWLObjectAllValuesFrom res = (OWLObjectAllValuesFrom) concept;

        for (Triple triple : new CopyOnWriteArrayList<Triple>(this.getTriples()))//as a list an element can be changed
        {
            if (triple.getRay().getRidge().getRoles().contains(res.getProperty())) {
                if (triple.getRay().getTip().getConcepts().contains(res.getFiller()) || triple.getRay().getTip().getConcepts().equals(res.getFiller())) {
                    st_copy.getTriples().add(triple);
                    continue;

                    //return;//because this triple is fresh and does not contains filler!
                } else {
                    ConceptLabel cl1 = triple.getCore();
                    Ray r = new Ray();
                    r.setRidge(triple.getRay().getRidge());
                    r.setTip(triple.getRay().getTip());
                    r.getTip().setIndividual(new HashSet<>(triple.getRay().getTip().getIndividual()));
                    Triple t_old = new Triple(cl1, r);

                    Triple t_new = new Triple(cl1, r);

                    Set<OWLClassExpression> tAug = data.getConceptsFromPrimitiveAxioms(
                            Sets.union(((OWLObjectAllValuesFrom) concept).getFiller().asConjunctSet(), data.getInitCore().getConcepts()),
                            triple.getRay().getTip().getConcepts());


                    t_new.getRay().getTip().getConcepts().add(((OWLObjectAllValuesFrom) concept).getFiller());

                    t_new.getRay().getTip().setIndividual(new HashSet<>());

                    t_new.getRay().getTip().getIndividual().addAll(triple.getRay().getTip().getIndividual());
                    st_copy.getTriples().add(t_new);
                    //use data.getConceptsForIndividuals if nominals
                    if (st_copy.isCoreValid(st_copy.getCore().getConcepts(), data) && st_copy.isCoreValidInd(st_copy, ontology)) {
                        //	this.getAddress().getSstar().add(st_copy);
                        mf.matchTriple(st_copy, t_new, this, t_old, this.getAddress(), ct, mf, data);
                    }

                    if (!Startype.isCoreValid(tAug, triple.getRay().getTip().getConcepts(), data)) //is it necessary ?
                    //if( !this.isComplexValid(tAug, triple.getRay().getTip().getConcepts(), data) )
                    {
                        st_copy.setValid(new Boolean(false));

                        return null;
                    }


                    changed = true;
                }
            }

        }
        st_copy.setNominal(this.isNominal());

        return st_copy;
    }

    // checks the applicability of the all rule
    public boolean isAllRule(OWLClassExpression concept, ReasoningData data) {
        //OWLPropertyExpression role = ((OWLObjectAllValuesFrom)concept).getProperty();
        //OWLClassExpression filler = ((OWLObjectAllValuesFrom)concept).getFiller();
        if (concept instanceof OWLObjectAllValuesFrom) {

            OWLObjectAllValuesFrom res = (OWLObjectAllValuesFrom) concept;
            for (Triple triple : this.getTriples()) {

                //Vector<Triple> vect =  new Vector<Triple>();
                //vect.add(triple);
                // ERROR: uk.ac.manchester.cs.owl.owlapi.OWLClassImpl cannot be cast to org.semanticweb.owlapi.model.OWLObjectAllValuesFrom
                //if(triple.getRay().getRidge().getRoles().contains(((OWLObjectAllValuesFrom)concept).getProperty() )) {
                // if(triple.getRay().getTip().getConcepts().containsAll( ((OWLObjectAllValuesFrom)concept).getFiller().asConjunctSet() ) ||
                //	  ((OWLObjectAllValuesFrom)concept).getFiller().equals(data.getTop()))  {


                if (triple.getRay().getRidge().getRoles().contains(res.getProperty()) || triple.getRay().getRidge().getRoles().equals(res.getProperty())) {
                    //

                    //   System.out.println("Signature of the concepts"+concept.getObjectPropertiesInSignature());
                    //Gets the object properties to  an object that has a signature in the signature and optionally the imports closure.

                    {
                        //  if(triple.getRay().getTip().getConcepts().containsAll( ((OWLQuantifiedRestriction<OWLClassExpression, OWLObjectPropertyExpression, OWLClassExpression>) concept).getFiller().asConjunctSet() ) ||
                        //  ((OWLQuantifiedRestriction<OWLClassExpression, OWLObjectPropertyExpression, OWLClassExpression>) concept).getFiller().equals(data.getTop()))

                        if (triple.getRay().getTip().getConcepts().contains(res.getFiller()) || triple.getRay().getTip().getConcepts().equals(res.getFiller())) {

                            continue;
                        } else {


                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }


    /*
     * If \forall S.C, R<=S, R transitive in the core, then this rule is applied
     */

    public boolean transRule(OWLClassExpression concept, SetMultimap<Triple, Triple> his, ReasoningData data) {
        OWLPropertyExpression role = ((OWLObjectAllValuesFrom) concept).getProperty();
        OWLClassExpression filler = ((OWLObjectAllValuesFrom) concept).getFiller();
        boolean changed = false;
        //We need a copy since triples in the startype may be updated
        for (Triple triple : new CopyOnWriteArrayList<Triple>(this.getTriples())) {
            for (OWLPropertyExpression trans : data.getRolesForTransRule(role)) {
                OWLClassExpression transAllConcept = data.getTransObjectAllValuesFrom(trans, filler);
                if (triple.getRay().getRidge().getRoles().contains(trans)) {
                    if (triple.getRay().getTip().getConcepts().contains(transAllConcept)) {
                        continue;
                    } else {
                        Set<OWLClassExpression> tipC = new HashSet<OWLClassExpression>(transAllConcept.asConjunctSet());
                        tipC.addAll(data.getInitCore().getConcepts());
                        tipC.add(transAllConcept);
                        Set<OWLClassExpression> tAug = data.getConceptsFromPrimitiveAxioms(tipC, triple.getRay().getTip().getConcepts());
                        if (!Startype.isCoreValid(tAug, triple.getRay().getTip().getConcepts(), data)) //is it necessary ?
                        //if( !this.isComplexValid(tAug, triple.getRay().getTip().getConcepts(), data) )
                        {
                            this.setValid(new Boolean(false));
                            return true;
                        }
                        //this.updateTriple(new Vector<Triple>(Collections.singleton(triple)), tAug,  his,  data);
                        this.updateTriple(triple, tAug, his, data);
                        changed = true;
                    }
                }
            }
        }
        return changed;
    }

    public boolean isTransRule(OWLClassExpression concept, ReasoningData data) {
        OWLPropertyExpression role = ((OWLObjectAllValuesFrom) concept).getProperty();
        OWLClassExpression filler = ((OWLObjectAllValuesFrom) concept).getFiller();
        for (Triple triple : this.getTriples()) {
            Vector<Triple> vect = new Vector<Triple>();
            vect.add(triple);
            for (OWLPropertyExpression trans : data.getRolesForTransRule(role)) {
                OWLClassExpression transAllConcept = data.getTransObjectAllValuesFrom(trans, filler);
                if (triple.getRay().getRidge().getRoles().contains(trans)) {
                    if (triple.getRay().getTip().getConcepts().contains(transAllConcept)) {
                        continue;
                    } else {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    //
    public boolean choiceRule(OWLClassExpression concept, SetMultimap<Triple, Triple> his,
                              Map<Startype, SetMultimap<Triple, Triple>> hisByUnsatL, ReasoningData data) {
        OWLPropertyExpression role = ((OWLObjectMaxCardinality) concept).getProperty();
        OWLClassExpression filler = ((OWLObjectMaxCardinality) concept).getFiller();
        OWLClassExpression fillerNNF = filler.getComplementNNF();
        boolean changed = false;
        for (Triple triple : new CopyOnWriteArrayList<Triple>(this.getTriples())) {
            //Vector<Triple> vect =  new Vector<Triple>();
            //vect.add(triple);
            if (triple.getRay().getRidge().getRoles().contains(role)) {
                if (triple.getRay().getTip().getConcepts().containsAll(filler.asConjunctSet()) ||
                        triple.getRay().getTip().getConcepts().containsAll(fillerNNF.asConjunctSet())) {
                    continue;
                } else {
                    Set<OWLClassExpression> tipC1 = new HashSet<OWLClassExpression>(filler.asConjunctSet());
                    tipC1.addAll(data.getInitCore().getConcepts());
                    tipC1.add(filler);
                    Set<OWLClassExpression> tAug1 = data.getConceptsFromPrimitiveAxioms(tipC1, triple.getRay().getTip().getConcepts());
                    Set<OWLClassExpression> tipC2 = new HashSet<OWLClassExpression>(fillerNNF.asConjunctSet());
                    tipC2.addAll(data.getInitCore().getConcepts());
                    tipC2.add(fillerNNF);
                    Set<OWLClassExpression> tAug2 = data.getConceptsFromPrimitiveAxioms(tipC2, triple.getRay().getTip().getConcepts());
                    boolean v1 = isCoreValid(tAug1, triple.getRay().getTip().getConcepts(), data); //isCoreValid(tAug1, triple.getRay().getTip().getConcepts(), data);
                    boolean v2 = isCoreValid(tAug2, triple.getRay().getTip().getConcepts(), data);
                    Triple f = null;
                    if (!v1 && !v2) {
                        this.setValid(new Boolean(false));
                        return true;
                    } else if (v1 && v2) //adds a new startype and changes the existing one
                    {
                        SetMultimap<Triple, Triple> newHis = HashMultimap.create();
                        Startype newSt = new Startype(this, his, newHis);
                        newSt.setSaturated(false);
                        for (Triple t : newSt.getTriples())
                            if (t.equals(triple))
                                f = t;
                        //newSt.updateTriple(vectTo, tAug2, newHis, data);//bugged his=>newHis
                        newSt.updateTriple(f, tAug2, newHis, data);//bugged his=>newHis
                        hisByUnsatL.put(newSt, newHis);
                        //System.out.println("NB ST SHAREDSTARTYPE CHOICE ="+ newSt.getTriples().size()+ ", NB HIS="+ newHis.size());
                        //this.updateTriple(new Vector<Triple>(Collections.singleton(triple)), tAug1, his, data);
                        this.updateTriple(triple, tAug1, his, data);
                        changed = true;
                    } else if (v1) {
                        //this.updateTriple(new Vector<Triple>(Collections.singleton(triple)), tAug1, his, data);`
                        this.updateTriple(triple, tAug1, his, data);
                        changed = true;
                    } else {
                        //this.updateTriple(new Vector<Triple>(Collections.singleton(triple)), tAug2, his, data);
                        this.updateTriple(f, tAug2, his, data);
                        changed = true;
                    }
                }
            }
        }//for
        return changed;
    }

    public boolean isChoiceRule(OWLClassExpression concept, ReasoningData data) {
        //not working
        //error:uk.ac.manchester.cs.owl.owlapi.OWLClassImpl cannot be cast to org.semanticweb.owlapi.model.OWLObjectMaxCardinality
        OWLPropertyExpression role = ((OWLObjectMaxCardinality) concept).getProperty();
        OWLClassExpression filler = ((OWLObjectMaxCardinality) concept).getFiller();
        OWLClassExpression fillerNNF = filler.getComplementNNF();
        for (Triple triple : this.getTriples()) {
            //Vector<Triple> vect =  new Vector<Triple>();
            //vect.add(triple);
            if (triple.getRay().getRidge().getRoles().contains(role)) {
                if (triple.getRay().getTip().getConcepts().containsAll(filler.asConjunctSet()) ||
                        triple.getRay().getTip().getConcepts().containsAll(fillerNNF.asConjunctSet())) {
                    continue;
                } else {
                    return true;
                }
            }
        }//for
        return false;
    }

    //"role = R" and "concept = C" and "N" in <= N R C
    //It returns true if there are not more N triples
    public boolean checkForMaxRays(OWLPropertyExpression role, OWLClassExpression concept, int N, ReasoningData data) {
        int c = 0;
        for (Triple triple : this.getTriples()) {
            if ((triple.getRay().getTip().getConcepts().containsAll(concept.asConjunctSet()) || concept.equals(data.getTop())) &&
                    triple.getRay().getRidge().getRoles().contains(role)) {
                c++;
                if (c > N) return false;
            }
        }
        return true;
    }

    //This method returns true iff triple1 and triple2 contain two distinct names.
    //If it returns true, we should not merge them
    public boolean checkForDistinctRays(Triple triple1, Triple triple2, ReasoningData data) {
        Set<OWLClassExpression> cs = new HashSet<OWLClassExpression>(this.getCore().getConcepts());
        //intersection
        cs.retainAll(data.getMinNames().keySet()); // max numbering concepts
        for (OWLClassExpression i : cs) {
            for (OWLClassExpression n1 : data.getMinNames().get(i)) {
                for (OWLClassExpression n2 : data.getMinNames().get(i)) {
                    if (!n1.equals(n2)) {
                        if (triple1.getRay().getTip().getConcepts().contains(n1) &&
                                triple2.getRay().getTip().getConcepts().contains(n2))
                            return true;
                    }
                }
            }
        }
        return false;
    }


    //This method return true iff ray1 and ray2 are present in pairs
    public boolean checkTriplePair(Triple triple1, Triple triple2, Set<Map<Triple, Triple>> pairs) {
        for (Map<Triple, Triple> pair : pairs) {
            if ((pair.containsKey(triple1) && pair.containsValue(triple2)) || (pair.containsKey(triple2) && pair.containsValue(triple1)))
                return true;
        }
        return false;
    }

    /*
     * Return a set of maps each of which is one pair of mergeable triples
     */
    public Set<Map<Triple, Triple>> selectPairsOfTriples(OWLPropertyExpression role, OWLClassExpression concept, ReasoningData data) {
        //Map<Triple, Triple> twoTriples =  null;
        Set<Map<Triple, Triple>> pairs = new HashSet<Map<Triple, Triple>>();
        for (Triple triple1 : this.getTriples()) {
            if ((triple1.getRay().getTip().getConcepts().contains(concept) || concept.equals(data.getTop())) &&
                    triple1.getRay().getRidge().getRoles().contains(role)) {
                for (Triple triple2 : this.getTriples()) {
                    if (!triple2.equals(triple1)) {
                        if ((triple2.getRay().getTip().getConcepts().contains(concept) || concept.equals(data.getTop())) &&
                                triple2.getRay().getRidge().getRoles().contains(role)) {
                            // triple1, triple2 mergeable and fresh in pairs
                            if (!checkForDistinctRays(triple1, triple2, data) && !checkTriplePair(triple1, triple2, pairs)) {
                                Map<Triple, Triple> twoTriples = new HashMap<Triple, Triple>();
                                twoTriples.put(triple1, triple2);
                                pairs.add(twoTriples);
                            }
                        }
                    }
                }
            }
        }
        return pairs;
    }

    public boolean maxRule(OWLClassExpression concept, SetMultimap<Triple, Triple> his,
                           Map<Startype, SetMultimap<Triple, Triple>> hisByUnsatL, ReasoningData data) {
        OWLPropertyExpression role = ((OWLObjectMaxCardinality) concept).getProperty();
        OWLClassExpression filler = ((OWLObjectMaxCardinality) concept).getFiller();
        int card = ((OWLObjectMaxCardinality) concept).getCardinality();
        //If no need of merging
        if (this.checkForMaxRays(role, filler, card, data)) {
            return false;
        }
        boolean satisfied = false;
        while (!satisfied) //"max concept" is satisfied when this.checkForMaxRays(role, filler, card) returns true
        {
            Set<Map<Triple, Triple>> pairs = this.selectPairsOfTriples(role, filler, data);
            // Return an invalid st if no merge can be performed
            if (pairs.size() == 0) {
                this.setValid(new Boolean(false));
                return true;
            }
            Map<Triple, Triple> firstPair = null;
            Triple key = null, val = null;
            for (Map<Triple, Triple> pair : pairs) {
                key = pair.keySet().iterator().next();
                val = pair.get(key);
                Set<OWLClassExpression> tipC = new HashSet<OWLClassExpression>(key.getRay().getTip().getConcepts());
                tipC.addAll(val.getRay().getTip().getConcepts()); //"key" and "val" are already valid
                tipC = data.getConceptsFromPrimitiveAxioms(tipC, new HashSet<OWLClassExpression>());
                if (!isCoreValid(tipC, new HashSet<OWLClassExpression>(), data))
                    continue;
                if (firstPair == null) {
                    firstPair = pair;
                    continue;
                }
                SetMultimap<Triple, Triple> newHis = HashMultimap.create(50, 50);
                Startype newSt = new Startype(this, his, newHis);
                newSt.setSaturated(false);
                newSt.mergeTriples(key, val, newHis, data);
                hisByUnsatL.put(newSt, newHis);
            }
            //Update this startype from the first pair
            if (firstPair == null) //If no pair is valid
            {
                this.setValid(new Boolean(false));
                return true;
            }
            //Taking the first pair
            key = (Triple) firstPair.keySet().toArray()[0];
            val = firstPair.get(key);
            this.mergeTriples(key, val, his, data);
            //System.out.println("NB ST SHAREDSTARTYPE  MAX ="+ this.getTriples().size()+ ", NB HIS="+ his.size());
            satisfied = this.checkForMaxRays(role, filler, card, data);
        }//while (!satisfied)
        return true;
    }

    // If >=n R C, <= n R C are in the core then min-rule applied on ">=n R C" has priority over "<=n R C"
    // If "concept"= (<= n R .C) is satisfied with m < n (i.e. there are exactly already  m rays containing R, C), then
    //     if  >=m R C, <= mR C are not in the core of this,  put them in the core
    //        creates a new startype containing <= (m-1) R C (put it in "hisByUnsatL";
    //        creates a new startype containing >= n R C (<= n R C is there already) with C_{} in the existing tips) ,
    //        creates a new startype containing  <= (n-1) R C
    //???
    public void minmaxRule(OWLClassExpression concept, Startype old,
                           SetMultimap<Startype, BiMap<Triple, Triple>> hisByUnsatL,
                           ReasoningData data) {

    }

    /*
     * It is supposed "this" contains no clash and "concept" is not satisfied
     * The goal is to satisfy "max concept" in the core of "this"
     *  Merges two triples into a new triple, replaces them with the new one and updates the keys of "his" (the values of his are not changed)
     *  It is impossible that newTriple equals an existing triple since (newLabelConcept_i, newLabelConcept_j) appears once in triple tips
     *
     *  triple evolves (by allRule, unionRule, ...) but his(triple) is never changed and equals null if triple is fresh by generating
     *  before saturating, values of "his" are never null
     *  his(triple) may have different values caused by merging
     *
     *  So, his(newTriple) = his(triple1) \/ his(triple2)  and removing multiple null (null by generating is not needed to be stored after merging)
     *  since, if his(triple1) = null and  his(triple1) = null then his(newTriple) = null (both are fresh)
     *         if his(triple1) <> null and his(triple2) = null  then his(newTriple) = his(triple1)
     *         if his(triple1) <> null and his(triple2) <> null  then his(newTriple) = his(triple1) \/ his(triple2)

    // It merges all pairs, create new (unsat) star-types until satisfied.
    // It should put unsat intermediate ("concept" is not satisfied yet) star-types in a temporary set
    // hisByUnsatL contains unsat startypes with "concept" satisfied and their history
    */
    public void thinh_maxRule(OWLClassExpression concept, SetMultimap<Triple, Triple> his,
                              Map<Startype, SetMultimap<Triple, Triple>> hisByUnsatL, ReasoningData data) {
        OWLPropertyExpression role = ((OWLObjectMaxCardinality) concept).getProperty();
        OWLClassExpression filler = ((OWLObjectMaxCardinality) concept).getFiller();
        int card = ((OWLObjectMaxCardinality) concept).getCardinality();
        // If no need to merge
        if (this.checkForMaxRays(role, filler, card, data)) {
            return;
        }
        SetMultimap<Triple, Triple> oldMap = HashMultimap.create();
        Startype changingSt = new Startype(oldMap, this); //oldMap is empty
        Map<Startype, SetMultimap<Triple, Triple>> tempHisByUnSatL = new HashMap<Startype, SetMultimap<Triple, Triple>>();

        tempHisByUnSatL.put(changingSt, oldMap);
        while (!tempHisByUnSatL.isEmpty()) {
            mergeInMaxRule(role, filler, card, tempHisByUnSatL, hisByUnsatL, data);
        }
        Startype st = hisByUnsatL.keySet().iterator().next();// toArray()[0]; Is hisByUnsatL always not empty ?
        SetMultimap<Triple, Triple> aMap = hisByUnsatL.remove(st); //Take the "his" corresponding to the startype ?

        this.getTriples().clear();

        for (Map.Entry<Triple, Triple> en : aMap.entries()) {
            Triple key = en.getKey();
            key.setCore(this.getCore());
            his.put(key, en.getValue());
        }
    }

    /*
     * Computes all indeterministic startypes ?
     */
    public void mergeInMaxRule(OWLPropertyExpression role,
                               OWLClassExpression filler, int card,
                               Map<Startype, SetMultimap<Triple, Triple>> tempHis,
                               Map<Startype, SetMultimap<Triple, Triple>> hisByUnsatL,
                               ReasoningData data) {
        Startype changingSt = (Startype) tempHis.keySet().toArray()[0];
        SetMultimap<Triple, Triple> oldMap = tempHis.remove(changingSt);
        // All possible pairs to merge
        Set<Map<Triple, Triple>> pairs = changingSt.selectPairsOfTriples(role, filler, data);
        // Return a set invalid if no merge can be performed
        if (pairs.size() == 0) {
            changingSt.setValid(new Boolean(false));
            return;
        }

        Triple key = null, val = null;
        for (Map<Triple, Triple> pair : pairs) {
            key = (Triple) pair.keySet().toArray()[0];
            val = pair.get(key);
            Set<OWLClassExpression> tipC = new HashSet<OWLClassExpression>(key.getRay().getTip().getConcepts());
            tipC.addAll(val.getRay().getTip().getConcepts());

            tipC = data.getConceptsFromPrimitiveAxioms(tipC,
                    new HashSet<OWLClassExpression>());

            if (!isCoreValid(tipC, new HashSet<OWLClassExpression>(), data))
            //if (!isComplexValid(tipC, new HashSet<OWLClassExpression>(), data))
            {
                continue;
            }
            SetMultimap<Triple, Triple> newMap = HashMultimap.create();
            SetMultimap<Triple, Triple> anotherMap = HashMultimap.create();
            Startype st = new Startype(anotherMap, changingSt);
            Triple newTr = changingSt.getMergedTriples(key, val, data);
            newTr.setCore(st.getCore());

            for (Triple t : anotherMap.keySet()) {
                Triple trr = (Triple) anotherMap.get(t).toArray()[0];
                Set<Triple> trInThis = oldMap.get(trr);
                if (trr == key || trr == val) {
                    st.getTriples().remove(t);
                    newMap.putAll(newTr, trInThis);
                } else
                    newMap.putAll(t, trInThis);
            }

            st.getTriples().add(newTr);
            st.setSaturated(false);
            if (st.checkForMaxRays(role, filler, card, data)) {
                hisByUnsatL.put(st, newMap);
            } else
                tempHis.put(st, newMap);
        }
    }

    /*
     * Produces the merged triple ?
     */
    public Triple getMergedTriples(Triple triple1, Triple triple2,
                                   ReasoningData data) {
        int hTr1 = triple1.hashCode();
        int hTr2 = triple2.hashCode();
        ConceptLabel cl = triple1.getRay().getTip().getNewConceptLabel(triple2.getRay().getTip().getConcepts());
        RoleLabel rl = triple1.getRay().getRidge().getNewRoleLabel(triple2.getRay().getRidge().getRoles(), data);
        Triple tr = new Triple(this.getCore(), new Ray(rl, cl));
        //hashcode = ID - hTr1 - hTr2 + tr.hashCode();
        this.setSaturated(false);
        return tr;
    }

    public boolean isMaxRule(OWLClassExpression concept, ReasoningData data) {
        OWLPropertyExpression role = ((OWLObjectMaxCardinality) concept)
                .getProperty();
        OWLClassExpression filler = ((OWLObjectMaxCardinality) concept)
                .getFiller();
        int card = ((OWLObjectMaxCardinality) concept).getCardinality();
        // If no need to merge
        if (this.checkForMaxRays(role, filler, card, data)) {
            return false;
        } else
            return true;
    }

    /*
     * Add concepts from "freshes" to "fresh"
     */
    public void addFreshCore(Set<OWLClassExpression> freshes, ReasoningData data) {
        for (OWLClassExpression i : freshes) {
            if (i.getClassExpressionType() == ClassExpressionType.OBJECT_ALL_VALUES_FROM ||
                    i.getClassExpressionType() == ClassExpressionType.OBJECT_MAX_CARDINALITY) {
                allmax.add(i);
            } else
                fresh.add(i);
        }
    }


    /*It removes "pro" from fresh concepts and adds it to "processedCoreconcepts"
      It ensures terminaison over startype expansion
      It does not care of "maxall"
     */
    public void addProcessedCore(OWLClassExpression pro, ReasoningData data) {
        this.getProcessedCore().add(pro);
        this.getFreshCore().remove(pro);
    }

    /*
     * cs1 : a new set of concepts
     * Assume that all concepts in cs2 are in NNF
     */
	/*public boolean isComplexValid(Set<OWLClassExpression> cs1, Set<OWLClassExpression> cs2, ReasoningData data) 
	{
		if( cs2.contains(data.getBottom()) || cs2.contains( data.getTop().getObjectComplementOf()) )
		{
		    return false;
		}
		for( OWLClassExpression i1 : cs1) 
		{
			if(i1.isOWLNothing() ) 
			{
			   return false;
		    }
		    //if( cs2.contains( i1.getObjectComplementOf() ) )
			if(cs2.contains( i1.getComplementNNF() ))
		    {
			   return false;
			}
	    }//for
	    return true;
	}*/
    public boolean isNominalValid(Set<OWLIndividual> inds, ReasoningData rd) {
        boolean valid = true;

        for (OWLIndividual ind1 : inds) {
            for (OWLIndividual ind2 : inds) {
                if (rd.getABox().getDiffIndAssers().containsEntry(ind1, ind2)) {

                    valid = false;
                }
            }
        }
        return valid;
    }

    public static boolean isCoreValid(Set<OWLClassExpression> cs1, Set<OWLClassExpression> cs2, ReasoningData data) {
        if (cs2.contains(data.getBottom()) || cs2.contains(data.getTop().getObjectComplementOf())) {
            return false;
        }
        for (OWLClassExpression i1 : cs1) {
            if (!i1.isAnonymous()) {
                if (i1.isOWLNothing()) {
                    return false;
                }
                if (cs2.contains(i1.getObjectComplementOf())) {
                    return false;
                }

                //i1 is \neg A
            } else if (i1.isClassExpressionLiteral()) {
                if (((OWLObjectComplementOf) i1).getOperand().isOWLThing()) {
                    return false;
                }

                if (cs2.contains(i1.getComplementNNF())) {
                    return false;
                }

            }
        }//for

        return true;
    }

    public static boolean isCoreValidInd(Startype st, OWLOntology ontology) {
        if (st.getCore().getIndividual() != null) {
            for (OWLIndividual ind : st.getCore().getIndividual()) {
                Set<OWLIndividual> diffinds;

                System.out.println("11111");
                System.out.println(ind.getClass());
                System.out.println("22222");
                diffinds = ind.getDifferentIndividuals(ontology);

                for (OWLIndividual diffind : diffinds)
                    if (st.getCore().getIndividual().contains(diffind)) {
                        return false;
                    }
            }
        }
        return true;
    }
	
	/*public boolean isComplexValid(Set<OWLClassExpression> cl,  ReasoningData data) //SharedCache cache,
	{       
		if( this.isValid()!=null && !this.isValid() ) 
		{	 
		    return false;
	    }
		//check for validity of "cl" itself 
	    if( !this.isComplexValid(cl, cl, data)  ) 
	    { 
		    return false;
	    }
 
		for (OWLClassExpression i1 :  cl) 
		{
		    if( i1.isOWLNothing()  ) 
		    {  
			      return false;
			}
		    if(this.getCore().getConcepts().contains( i1.getComplementNNF() ))
		    {
			   return false;
			}
		}//for 
		return true;
	}*/

    public boolean isCoreValid(Set<OWLClassExpression> cl, ReasoningData data) {
        if (this.isValid() != null && !this.isValid()) {
            return false;
        }
        //check for validity of "cl" itself
        if (!Startype.isCoreValid(cl, cl, data)) {
            return false;
        }

        for (OWLClassExpression i1 : cl) {
            if (!i1.isAnonymous()) {
                if (i1.isOWLNothing()) {
                    return false;
                }

                if (this.getCore().getConcepts().contains(i1.getObjectComplementOf())) {
                    return false;
                }
            } else if (i1.isClassExpressionLiteral()) {
                if (((OWLObjectComplementOf) i1).getOperand().isOWLThing())
                    return false;

                if (this.getCore().getConcepts().contains(i1.getComplementNNF())) {
                    return false;
                }
            }
        }//for
        return true;
    }

    /*
     * Some triples collapse after removing nominal
     * If there is no nominal like \exists R {o} then the skeleton st remains sat if this st is sat
     */
    public Startype skeletonize(ReasoningData data) {
        Startype st = new Startype();
        st.setCore(this.getCore().removeNominals(), data);
        st.fresh.addAll(this.getFreshCore());
        st.processed.addAll(this.getProcessedCore());
        st.allmax.addAll(this.getAllMaxCore());
        for (Triple i : this.getPredTriples()) {
            Triple nt = new Triple(i);
            nt.getRay().setTip(nt.getRay().getTip().removeNominals());
            nt.getCore().removeNominals();
            st.addTripleToList(nt, st.isPredTriple(i));
        }
        st.setNominal(false);
        st.hashcode = st.sumCode();
        return st;
    }
    /*
     * Checks if there is a concept from cs2 that contradicts a concept from cs1
     */
    /*public boolean isValid(Set<OWLClassExpression> cs1, Set<OWLClassExpression> cs2, ReasoningData data) 
    {            
    	if( cs2.contains(data.getBottom()) || cs2.contains( data.getTop().getObjectComplementOf()) )
		{
		       return false;
		}
		for(OWLClassExpression i1 : cs1) 
		{
		   if( !i1.isAnonymous()  ) 
		   {
		      if(i1.isOWLNothing() ) 
		      {
			       return false;
			  }
			  if( cs2.contains( i1.getObjectComplementOf() ) )
			  {
			       return false;
			  }
			   
		     //i1 is \neg A	
		   } else if(i1.isClassExpressionLiteral()) 
		   {
		       if(((OWLObjectComplementOf)i1).getOperand().isOWLThing() )
		       {       
			       return false;
			   }
		        
			   if(cs2.contains( i1.getComplementNNF() ))
			   {   
			       return false;
			   }
			
		   } else if(data.isL1LiteralExpression(i1)) 
		   {
		        if(cs2.contains( i1.getComplementNNF()) )
		        {	            
			       return false;
		        }
		   }  
		}//for
		//System.out.println("isValid cs1, cs2= true") ;
		return true;
    } */

    /*
     * Checks if "cl" has a clash with the core of startype
     */
	/*public boolean isValid(Set<OWLClassExpression> cl,  ReasoningData data) //SharedCache cache,
	{       
		//System.out.println("isValid cl") ;
		//ManchesterOWLSyntaxOWLObjectRendererImpl render = new ManchesterOWLSyntaxOWLObjectRendererImpl();
		if( this.isValid()!=null && !this.isValid() ) 
		{	 
		    return false;
	    }
		//check for validity of "cl" itself 
	    if( !this.isValid(cl, cl, data)  ) 
	    { 
		    return false;
	    }
 
		for (OWLClassExpression i1 :  cl) 
		{
		   if( !i1.isAnonymous()  ) 
		   {
		      if( i1.isOWLNothing()  ) 
		      {  
			      return false;
			  }		 
		       
		      if(this.getCore().getConcepts().contains(i1.getObjectComplementOf()))
		      {                	
		    	//System.out.println("False") ;
			    return false;
			  }
		   } else if( i1.isClassExpressionLiteral()  ) 
		   {
			 if( ((OWLObjectComplementOf)i1).getOperand().isOWLThing() )
			    return false;
			  
			 if( this.getCore().getConcepts().contains(i1.getComplementNNF()))
			 {    	  
				   return false;
		     }
		   } else if(data.isAllL1LiteralExpression(i1)) 
		   {
		      
			 if( this.getCore().getConcepts().contains( i1.getComplementNNF()) )
			 {
			    return false;
		     } 
	       } else if(data.isMinL1LiteralExpression(i1)) 
	       {
		      
	    	 if( this.getCore().getConcepts().contains ( i1.getComplementNNF()) )
	    	 {       
			   return false;
		     }
		   } 
		}//for 
		//System.out.println("isValid cl OK") ;
		return true;
	}
	
	/*public boolean isComplexValid(ConceptLabel x, ReasoningData data) 
	{   
		if( isValid()!=null && !isValid() ) 
		{      
		    return false;
		}
		for (OWLClassExpression i1 :  x.getConcepts() ) 
		{
			if( !isComplexValid( new HashSet<OWLClassExpression>(Collections.singleton(i1)), x.getConcepts(), data) )
				return false;
		}
		return true;
	}*/

    /*
     *  Returns "true" if the core contains no clash
     */
    public boolean isValid(ConceptLabel x, ReasoningData data) {
        //System.out.println("isValid core") ;
        //A startype may be invalid even if it is not saturated
        if (isValid() != null && !isValid()) {
            return false;
        }
        for (OWLClassExpression i1 : x.getConcepts()) {
            if (!isCoreValid(new HashSet<OWLClassExpression>(Collections.singleton(i1)), x.getConcepts(), data))
                return false;
        }
        return true;
    }

    public Set<OWLClassExpression> getFreshCore() {
        return this.fresh;
    }

    public Set<OWLClassExpression> getProcessedCore() {
        return this.processed;
    }

    public Set<OWLClassExpression> getAllMaxCore() {
        return this.allmax;
    }

    public List<Triple> getTriples() {
        return this.triples;
    }

    public void setSaturated() {
        this.isSaturated = true;
    }

    public void setSaturated(boolean b) {
        this.isSaturated = b;
    }

    public boolean isSaturated() {
        return isSaturated;
    }

    public void setNominal(boolean b) {
        this.isNominal = b;
    }

    public boolean isNominal() {
        return isNominal;
    }

    public List<Triple> getPredTriples() {
        return this.predTriples;
    }

    public boolean isPredTriple(Triple t) {
        if (this.getPredTriples().contains(t))
            return true;
        else
            return false;
    }

    public List<Triple> getSuccTriples() {
        List<Triple> succ = new ArrayList<Triple>(this.getTriples());
        succ.removeAll(this.getPredTriples());
        return succ;
    }

    public void setValid(Boolean b) {
        if (b == null)
            this.isValid = null;
        else
            this.isValid = new Boolean(b.booleanValue());
    }

    public Boolean isValid() {
        return this.isValid;
    }

    public int getIdS() {
        return idS;
    }

    public void setIdS(int idS) {
        this.idS = idS;
    }

    public void incIdS() {
        this.idS++;
    }


    //"equals" is called only if hashCodes of two objects are the same

    public int sumCode() {
        long hash = 1234;
        if (this.getTriples().isEmpty())
            hash += this.getCore().hashCode() * 2;
        else
            for (Triple t : this.getTriples()) {
                hash += t.hashCode();
            }
        return (int) (hash);
    }

    @Override
    public int hashCode() {
        return hashcode;
    }


    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        Startype other = (Startype) obj;

        if (!this.getCore().equals(other.getCore())) {
            return false;
        }

        if (!this.getTriples().containsAll(other.getTriples()) || !other.getTriples().containsAll(this.getTriples())) {
            return false;
        }
        return true;
    }

    public void toXML(PrintWriter writer) {
        //ManchesterOWLSyntaxOWLObjectRendererImpl render = new ManchesterOWLSyntaxOWLObjectRendererImpl();
        writer.print("<startype hashcode='" + this.getIdS() + "' sat='" + this.isSaturated + "'> \n");
        for (Triple co : this.getTriples()) {
            co.toXML(writer);
        }
        writer.print("</startype>\n");
    }

    /*	public Startype subsetRule(OWLClassExpression cl) {
            Startype copy_st=this;
            if( cl= null ) {

            }
            return copy_st;
        }*/
    public boolean isSaturated(Layer layer, ReasoningData rd, CompressedTableau ct) {

        boolean saturated = true;

        for (OWLClassExpression cl : this.getCore().getConcepts()) {
            //System.out.println("forall: "+this.isAllRule(cl, rd)+" is some "+this.isSomeRule(cl, rd, layer,ct)+" is union "+this.isUnionRule(cl, rd)+" is intersection "+this.isIntersectionRule(cl, rd));
            // System.out.println(" is union "+this.isUnionRule(cl, rd)+" is intersection "+this.isIntersectionRule(cl, rd));
            if (this.isAllRule(cl, rd) || this.isSomeRule(cl, rd, layer, ct) || this.isUnionRule(cl, rd) || this.isIntersectionRule(cl, rd)) {
                //+
                saturated = false;

            }

        }
        return saturated;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        //sb.append("SharedStartype, valid = " + this.isValid() + ", level= "+ evolLevel +", saturated =" + this.isSaturated()+ ", nominal =" + this.isNominal()+ System.getProperty("line.separator"));
        sb.append("\nStartype, hashcode=" + hashcode + ", valid = " + this.isValid() + ", saturated =" + this.isSaturated() + ", nominal =" + this.isNominal() + System.getProperty("line.separator"));
        sb.append("Core =" + System.getProperty("line.separator")); //", distance =" +this.getDistance()+
        sb.append(this.getCore().toString());
        sb.append("\nList of triples = (" + getTriples().size() + ")" + System.getProperty("line.separator"));
        int i = 0;
        for (Triple tr : this.getTriples()) {
            if (this.isPredTriple(tr))
                sb.append("\nPredecessor Triple, inverse hashcode= " + tr.getInverseOf().hashCode() + ", " + i + "=" + tr.toString());
            else
                sb.append("\nSuccessor Triple " + i + "=" + tr.toString());
            i++;
        }

        return sb.toString();
    }

    public void setTriples(List<Triple> triples) {
        this.triples = triples;
    }

    public Layer getAddress() {
        // TODO Auto-generated method stub
        return address;
    }

    public void setAddress(Layer layer) {
        // TODO Auto-generated method stub
        this.address = layer;

    }

}
