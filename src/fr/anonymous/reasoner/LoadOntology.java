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
import java.io.File;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.ClassExpressionType;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLDataPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLDataPropertyExpression;
import org.semanticweb.owlapi.model.OWLDifferentIndividualsAxiom;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLLiteral;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLProperty;
import org.semanticweb.owlapi.model.OWLPropertyExpression;
import org.semanticweb.owlapi.model.OWLSameIndividualAxiom;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLSubDataPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubObjectPropertyOfAxiom;
import org.semanticweb.owlapi.util.DLExpressivityChecker;
import com.google.common.collect.SetMultimap;
import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;

public class LoadOntology {
    private OWLOntology ontology;
    private static OWLDataFactory factory = new OWLDataFactoryImpl();
    private ReasoningData data;
    private BinaryAbsorption absor;
    private LoadingLinkeys loadlk;
    private LKBox LK;

    public LoadOntology(OWLOntology onto, int strategy) {
        data = new ReasoningData();
        absor = new BinaryAbsorption();
        loadlk = new LoadingLinkeys();
        LK = new LKBox();
        Set<OWLOntology> sOnto = new HashSet<>();
        sOnto.add(onto);
        DLExpressivityChecker expr = new DLExpressivityChecker(sOnto);
        List<DLExpressivityChecker.Construct> constructs = null;
        try {
            constructs = expr.getConstructs();
        } catch (Exception ex) {
            ex.printStackTrace();
        }
        for (DLExpressivityChecker.Construct c : constructs) {
            if (c.toString().equals("C") || c.toString().equals("S"))
                data.setUnion(true);
            if (c.toString().equals("E"))
                data.setSome(true);
            if (c.toString().equals("I"))
                data.setInverse(true);
            if (c.toString().equals("H"))
                data.setHierarchy(true);
            if (c.toString().equals("F") || c.toString().equals("Q"))
                data.setCardinality(true);
            if (c.toString().equals("+"))
                data.setTransitive(true);
            if (c.toString().equals("O"))
                data.setNominal(true);
            if (c.toString().equals("D"))
                data.setDatatype(true);
        }
        this.ontology = onto;
        data.setTop(factory.getOWLThing());
        data.setBottom(factory.getOWLNothing());
        data.setStrategy(strategy);
        this.getIndividuals(data);
        this.getAtomicConcepts(data);// store initial concepts
        this.getAtomicRoles(data); // store object, data properties with attributes
        this.getConceptAxioms(data);
        //"absor" will fill "data"
        absor.absorbBinaryAxioms(data);
        this.makeClosureByRole(data);
        this.getAssertions(data);
        this.createEmptyInitCores(data);
        data.getABox().init(data);// computes transitive individual equalities
    }

    public LoadOntology(OWLOntology onto, int strategy, File f) {
        data = new ReasoningData();
        absor = new BinaryAbsorption();
        loadlk = new LoadingLinkeys();
        LK = new LKBox();
        Set<OWLOntology> sOnto = new HashSet<>();
        sOnto.add(onto);
        DLExpressivityChecker expr = new DLExpressivityChecker(sOnto);
        List<DLExpressivityChecker.Construct> constructs = null;
        try {
            constructs = expr.getConstructs();
        }
        catch (Exception ex) {
            ex.printStackTrace();
        }
        for (DLExpressivityChecker.Construct c : constructs) {
            if (c.toString().equals("C") || c.toString().equals("S"))
                data.setUnion(true);
            if (c.toString().equals("E"))
                data.setSome(true);
            if (c.toString().equals("I"))
                data.setInverse(true);
            if (c.toString().equals("H"))
                data.setHierarchy(true);
            if (c.toString().equals("F") || c.toString().equals("Q"))
                data.setCardinality(true);
            if (c.toString().equals("+"))
                data.setTransitive(true);
            if (c.toString().equals("O"))
                data.setNominal(true);
            if (c.toString().equals("D"))
                data.setDatatype(true);
        }
        this.ontology = onto;
        data.setTop(factory.getOWLThing());
        data.setBottom(factory.getOWLNothing());
        data.setStrategy(strategy);
        this.getIndividuals(data);
        this.getAtomicConcepts(data);// store initial concepts
        this.getAtomicRoles(data); // store object, data properties with attributes
        this.getConceptAxioms(data);
        //"absor" will fill "data"
        absor.absorbBinaryAxioms(data);
        this.makeClosureByRole(data);
        this.getAssertions(data);
        data.getABox().init(data);// computes transitive individual equalities
        loadlk.EDOALtoLKs(f);
        if (!loadlk.EDOALtoLKs(f).isEmpty()) {
            data.containsLk(true);
            LK.setLks(loadlk.EDOALtoLKs(f));
            data.setLK(LK);
        }
    }


    public LoadOntology() {
        // TODO Auto-generated constructor stub
    }

    public BinaryAbsorption getAbsorption() {
        return absor;
    }

    // It is not needed to add "lazyConcepts" to "initCore"
    //    since the left side of each primitive axiom is atomic (not a UNION)
    // If data.getGenConceptAxioms() is empty, there is an individual "o" included in "TOP". It is done in "getIndividuals"
    public void createEmptyInitCores(ReasoningData data) {
        Set<OWLClassExpression> label = new HashSet<>();
        for (ConceptAxiom ax : absor.getGenConceptAxioms()) {
            label.addAll(ax.getNNF().asConjunctSet());
        }
        ConceptLabel init = new ConceptLabel(label);
        data.setInitCore(init);
        ConceptLabel emptyCore = new ConceptLabel();
        data.setEmptyCore(emptyCore);
    }

    /*
     * Returns the number of disjunctions at top-level
     * Not yet taking into account max, min , all
     */
    public int getNbIndet(Set<OWLClassExpression> cs) {
        int max = 0;
        Set<OWLClassExpression> addedC = new HashSet<>(cs);

        for (OWLClassExpression c : cs) {
            addedC.addAll(data.getConceptsFromPrimitiveAxioms(c.asConjunctSet(), data.getInitCore().getConcepts()));
        }
        for (OWLClassExpression c : addedC) {
            if (c.getClassExpressionType() == ClassExpressionType.OBJECT_UNION_OF) {
                max = max + (c.asDisjunctSet().size() - 1);
                int m = 0;
                for (OWLClassExpression cc : c.asDisjunctSet()) {
                    Set<OWLClassExpression> res = data.getConceptsFromPrimitiveAxioms(cc.asConjunctSet(), data.getInitCore().getConcepts());
                    for (OWLClassExpression w : res)
                        if (w.getClassExpressionType() == ClassExpressionType.OBJECT_UNION_OF && w.asDisjunctSet().size() > m)
                            m = w.asDisjunctSet().size();
                }
                max += m;
            }

        }
        return max;
    }

    /*
     * This class performs absorption and stores axioms in BinaryAbsorption which,
     *  in turn, transforms and stores them in ReasoningData
     */
    private void getConceptAxioms(ReasoningData data) {

        OWLClassExpression superClass = null;
        OWLClassExpression subClass = null;
        // for each class axiom in the ontology
        for (OWLAxiom classAxiom : ontology.getAxioms()) {
            //HERE for Tbox
            if (classAxiom.getAxiomType().equals(AxiomType.SUBCLASS_OF)) {
                subClass = ((OWLSubClassOfAxiom) classAxiom).getSubClass().getNNF();
                superClass = ((OWLSubClassOfAxiom) classAxiom).getSuperClass().getNNF();
                if (subClass.isOWLThing())
                    data.getRightConjunctsOfTop().add(superClass);
                if (subClass.isOWLNothing()) //tautology
                    continue;
                if (subClass.isClassExpressionLiteral()) // including negated subClass
                {
                    if (subClass.isAnonymous() && ((OWLObjectComplementOf) subClass).getOperand().isOWLThing())  // \neg \top = \bot <= X
                        // every thing is subset of the OWLThing class
                        continue;
                    else
                        absor.getAtomicAxioms().add(new ConceptAxiom(subClass, superClass));
                }
                else if (absor.containsOnlyInterSomeLiteral(subClass)) // including negated subClass
                {
                    Set<ConceptAxiom> atomicAxs = absor.absorbAxiom(new ConceptAxiom(subClass, superClass), data);
                    absor.getAtomicAxioms().addAll(atomicAxs);
                }
                else if (absor.isAbsorbableInterLiteral(subClass)) {
                    Set<ConceptAxiom> s = absor.absorbPart(new ConceptAxiom(subClass, superClass), data);
                    absor.getAtomicAxioms().addAll(s);
                }
                else {
                    absor.getGenConceptAxioms().add(new ConceptAxiom(subClass, superClass));
                }
            }
            /* dealing with the disjoint axioms */
            // C disjoint D => C < not D
            if (classAxiom.getAxiomType().equals(AxiomType.DISJOINT_CLASSES)) {
                OWLDisjointClassesAxiom disjAxiom = (OWLDisjointClassesAxiom) classAxiom;
                Set<OWLSubClassOfAxiom> subClassOfAxioms = disjAxiom.asOWLSubClassOfAxioms();

                for (OWLSubClassOfAxiom ax : subClassOfAxioms) {
                    subClass = ax.getSubClass().getNNF();
                    superClass = ax.getSuperClass().getNNF();
                    if (subClass.isOWLThing())
                        data.getRightConjunctsOfTop().add(superClass);
                    if (subClass.isClassExpressionLiteral()) // including negated subClass
                    {
                        if (subClass.isAnonymous() && ((OWLObjectComplementOf) subClass).getOperand().isOWLThing()) // \neg \top = \bot <= X
                            continue;
                        else
                            absor.getAtomicAxioms().add(new ConceptAxiom(subClass, superClass)); // was a bug superClass, superClass
                    } //BinaryAbsorption

                    else if (absor.containsOnlyInterSomeLiteral(subClass)) // including negated subClass
                    {
                        Set<ConceptAxiom> atomicAxs = absor.absorbAxiom(new ConceptAxiom(subClass, superClass), data);
                        absor.getAtomicAxioms().addAll(atomicAxs);
                    } else if (absor.isAbsorbableInterLiteral(subClass))    // including negated subClass
                    {
                        Set<ConceptAxiom> s = absor.absorbPart(new ConceptAxiom(subClass, superClass), data);
                        absor.getAtomicAxioms().addAll(s);
                    } else {
                        absor.getGenConceptAxioms().add(new ConceptAxiom(subClass, superClass));
                    }
                }
            }

            /* dealing with equivalence axioms */
            if (classAxiom.getAxiomType().equals(AxiomType.EQUIVALENT_CLASSES)) {
                List<OWLClassExpression> classes = ((OWLEquivalentClassesAxiom) classAxiom).getClassExpressionsAsList();
                subClass = classes.get(0).getNNF();
                superClass = classes.get(1).getNNF();
                if (subClass.isOWLThing())
                    data.getRightConjunctsOfTop().add(superClass);
                //C= D => C <= D and D <= C
                if (subClass.isClassExpressionLiteral()) // including negated subClass
                {
                    if ((!subClass.isAnonymous() && !subClass.isOWLNothing()) || // different from  \bot <=
                            (subClass.isAnonymous() && !((OWLObjectComplementOf) subClass).getOperand().isOWLThing())) // different from \neg \top <= X
                    {
                        if (!subClass.isAnonymous()) {
                            absor.getAtomicAxioms().add(new ConceptAxiom(subClass, superClass));
                        } else
                            absor.getGenConceptAxioms().add(new ConceptAxiom(subClass, superClass));
                    }
                }//BinaryObsorption
                else if (absor.containsOnlyInterSomeLiteral(subClass)) {
                    Set<ConceptAxiom> atomicAxs = absor.absorbAxiom(new ConceptAxiom(subClass, superClass), data);
                    //absor.getEquivAtomicAxioms().addAll(atomicAxs);
                    absor.getAtomicAxioms().addAll(atomicAxs);
                } else if (absor.isAbsorbableInterLiteral(subClass)) {
                    Set<ConceptAxiom> s = absor.absorbPart(new ConceptAxiom(subClass, superClass), data);
                    //absor.getEquivAtomicAxioms().addAll(s);
                    absor.getAtomicAxioms().addAll(s);
                } else {
                    absor.getGenConceptAxioms().add(new ConceptAxiom(subClass, superClass));
                }

                // other direction
                if (superClass.isClassExpressionLiteral()) // including negated superClass
                {
                    if ((!superClass.isAnonymous() && !superClass.isOWLNothing()) || // different from  \bot <= X
                            (superClass.isAnonymous() && !((OWLObjectComplementOf) superClass).getOperand().isOWLThing())) // different from \neg \top <= X
                    {
                        if (!superClass.isAnonymous()) {
                            absor.getAtomicAxioms().add(new ConceptAxiom(superClass, subClass));
                        } else
                            absor.getGenConceptAxioms().add(new ConceptAxiom(superClass, subClass));
                    }
                } else if (absor.containsOnlyInterSomeLiteral(superClass)) {
                    Set<ConceptAxiom> atomicAxs = absor.absorbAxiom(new ConceptAxiom(superClass, subClass), data);
                    absor.getAtomicAxioms().addAll(atomicAxs);
                } else if (absor.isAbsorbableInterLiteral(superClass)) {
                    Set<ConceptAxiom> s = absor.absorbPart(new ConceptAxiom(superClass, subClass), data);
                    absor.getAtomicAxioms().addAll(s);
                } else if (subClass.isClassExpressionLiteral()) // A = C
                {
                    if ((!subClass.isAnonymous() && !subClass.isOWLThing()) || // different from  \top >= X
                            (subClass.isAnonymous() && !((OWLObjectComplementOf) subClass).getOperand().isOWLNothing())) // different from \neg \bot >= X
                    {
                        //System.out.println("superClass = "+ (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(superClass) );
                        if (superClass.getClassExpressionType() == ClassExpressionType.OBJECT_UNION_OF) {
                            for (OWLClassExpression cl : superClass.asDisjunctSet()) {
                                //System.out.println("cl === "+ (new ManchesterOWLSyntaxOWLObjectRendererImpl()).render(cl) );
                                if (!cl.isAnonymous()) {
                                    absor.getAtomicAxioms().add(new ConceptAxiom(cl, subClass));

                                } else if (absor.containsOnlyInterSomeLiteral(cl)) {
                                    Set<ConceptAxiom> atomicAxs = absor.absorbAxiom(new ConceptAxiom(cl, subClass), data);
                                    absor.getAtomicAxioms().addAll(atomicAxs);

                                } else if (absor.isAbsorbableInterLiteral(cl)) {
                                    Set<ConceptAxiom> s = absor.absorbPart(new ConceptAxiom(cl, subClass), data);
                                    absor.getAtomicAxioms().addAll(s);

                                } else {
                                    absor.getGenConceptAxioms().add(new ConceptAxiom(cl, subClass));
                                }
                            }
                        } else {
                            //OWLClassExpression notSubClass = factory.getOWLObjectComplementOf(subClass).getNNF();
                            //OWLClassExpression notSuperClass = factory.getOWLObjectComplementOf(superClass).getNNF();
                            //absor.getEquivAtomicAxioms().add(new ConceptAxiom(notSubClass, notSuperClass));
                            absor.getGenConceptAxioms().add(new ConceptAxiom(superClass, subClass));
                        }
                    }
                } else {
                    absor.getGenConceptAxioms().add(new ConceptAxiom(superClass, subClass));
                }
            }//EQUIV
        }//for

        for (OWLClassExpression concept : data.getRightConjunctsOfTop())
            data.getRightConjunctsOfTop().addAll(concept.asConjunctSet());
    }

    private void getIndividuals(ReasoningData data) {
        //The individuals stored in ABox, not ReasoningData
        data.getABox().getInitInds().addAll(ontology.getIndividualsInSignature());
        if (data.getABox().getInitInds().isEmpty()) {
            data.setDummyInd();
            data.getABox().getInitInds().add(data.getDummyInd());
            data.getABox().getConceptsByInd().put(data.getDummyInd(), data.getTop());
        }
    }

    private void getAtomicConcepts(ReasoningData data) {
        data.getInitialAtomicConcepts().addAll(ontology.getClassesInSignature());
    }

    /*
     * Defines also attribute for each role name
     */
    private void getAtomicRoles(ReasoningData data) {
        for (OWLProperty prop : ontology.getObjectPropertiesInSignature()) {
            boolean tr = false;
            RoleAttributes attr = new RoleAttributes(false, false, false, tr, false);
            data.getObjectPropWithAttr().put((OWLObjectPropertyExpression) prop, attr);
        }

        for (OWLProperty prop : ontology.getDataPropertiesInSignature()) {
            RoleAttributes attr = new RoleAttributes(false, false, true, false, false);
            data.getDataPropWithAttr().put((OWLDataPropertyExpression) prop, attr);
        }
    }

    /*
     * Update ABox in DataReasoning
     */
    private void getAssertions(ReasoningData data) {
        for (OWLIndividual individual : data.getABox().getInitInds()) {
            for (OWLClassAssertionAxiom as : ontology.getClassAssertionAxioms(individual))
                data.getABox().getConceptsByInd().put(individual, as.getClassExpression());

            for (OWLObjectPropertyAssertionAxiom asser : ontology.getObjectPropertyAssertionAxioms(individual)) {
                Map<OWLObjectPropertyExpression, OWLIndividual> m = new HashMap<>();
                m.put(asser.getProperty(), asser.getObject());
                data.getABox().getConceptObjeAssertBySource().put(individual, m);
                Map<OWLObjectPropertyExpression, OWLIndividual> m1 = new HashMap<>();
                m1.put(asser.getProperty(), asser.getSubject());
                data.getABox().getConceptObjeAssertByTarget().put(asser.getObject(), m1);
            }
            for (OWLDataPropertyAssertionAxiom asser : ontology.getDataPropertyAssertionAxioms(individual)) {
                if (asser.getSubject().equals(individual)) {
                    Map<OWLDataPropertyExpression, OWLLiteral> m = new HashMap<>();
                    m.put(asser.getProperty(), asser.getObject());
                    data.getABox().getConceptDataAssertBySource().put(individual, m);

                    Map<OWLDataPropertyExpression, OWLIndividual> m2 = new HashMap<>();
                    m2.put(asser.getProperty(), individual);
                    data.getABox().getConceptDataAssertByTarget().put(asser.getObject(), m2);
                }
            }
            for (OWLSameIndividualAxiom asser : ontology.getSameIndividualAxioms(individual)) {
                List<OWLIndividual> is = asser.getIndividualsAsList();
                data.getABox().getSameIndAssers().put(is.get(0), is.get(1));
            }
            for (OWLDifferentIndividualsAxiom asser : ontology.getDifferentIndividualAxioms(individual)) {
                List<OWLIndividual> is = asser.getIndividualsAsList();
                data.getABox().getDiffIndAssers().put(is.get(0), is.get(1));
            }
        }
    }

    /*
     *  Builds getSubClosureByRole and getSuperClosureByRole,
     *  i.e. if R <= S, R <= U then R: S, U
     *  If R- <= S- then S is in the closure of R
     */
    private void makeClosureByRole(ReasoningData data) {
        Set<OWLPropertyExpression> rolesInHierarchy = new HashSet<>();
        for (OWLObjectProperty property : ontology.getObjectPropertiesInSignature()) {
            for (OWLSubObjectPropertyOfAxiom axiom : ontology.getObjectSubPropertyAxiomsForSubProperty(property)) {
                rolesInHierarchy.add(axiom.getSubProperty());
                rolesInHierarchy.add(axiom.getSuperProperty());
            }
        }
        for (OWLDataProperty property : ontology.getDataPropertiesInSignature()) {
            //rolesInHierarchy.add(property);//self subsumption which are all properties
            for (OWLSubDataPropertyOfAxiom axiom : ontology.getDataSubPropertyAxiomsForSubProperty(property)) {
                rolesInHierarchy.add(axiom.getSubProperty());
                rolesInHierarchy.add(axiom.getSuperProperty());
            }
        }
        for (OWLPropertyExpression role : rolesInHierarchy) {
            Set<OWLPropertyExpression> supers = new HashSet<>();
            Set<OWLPropertyExpression> subs = new HashSet<>();
            supers.add(role);
            subs.add(role);
            if (!role.isDataPropertyExpression()) {
                // Gets all axioms (role <= sup )
                Set<OWLSubObjectPropertyOfAxiom> objAxs = ontology.getObjectSubPropertyAxiomsForSubProperty((OWLObjectPropertyExpression) role);
                //For each (role <= sup )
                for (OWLSubObjectPropertyOfAxiom ax : objAxs) {
                    supers.add(ax.getSuperProperty());
                    // if role- <= R then add R- to supers(role)
                    if (role instanceof OWLObjectPropertyExpression && !((OWLObjectPropertyExpression) role).getNamedProperty().equals(role)) {
                        supers.add(ax.getSuperProperty().getInverseProperty());
                    }
                }
                // Gets all axioms (sub <= role  )
                objAxs = ontology.getObjectSubPropertyAxiomsForSuperProperty((OWLObjectPropertyExpression) role);
                for (OWLSubObjectPropertyOfAxiom ax : objAxs) {
                    subs.add(ax.getSubProperty());
                    // if R <= role-  then add R- to subs(role)
                    if (role instanceof OWLObjectPropertyExpression && !((OWLObjectPropertyExpression) role).getNamedProperty().equals(role)) {
                        subs.add(ax.getSubProperty().getInverseProperty());
                    }
                }
            } else if (role.isDataPropertyExpression()) {
                Set<OWLSubDataPropertyOfAxiom> objAxs1 = ontology.getDataSubPropertyAxiomsForSubProperty((OWLDataProperty) role);
                for (OWLSubDataPropertyOfAxiom ax : objAxs1) {
                    supers.add(ax.getSuperProperty());
                }
                objAxs1 = ontology.getDataSubPropertyAxiomsForSuperProperty((OWLDataProperty) role);
                for (OWLSubDataPropertyOfAxiom ax : objAxs1) {
                    subs.add(ax.getSubProperty());
                }
            }
            data.getSuperClosureByRole().putAll(role, supers);
            data.getSubClosureByRole().putAll(role, subs);
        }

        // compute closure
        Set<OWLPropertyExpression> rolesPinv = new HashSet<>(data.getObjectPropWithAttr().keySet());
        rolesPinv.addAll(data.getDataPropWithAttr().keySet());
        Set<OWLPropertyExpression> tmp = new HashSet<>(rolesPinv);
        //tmp contains the initial roles in the hierarchy
        //This loop adds the inverse roles
        for (OWLPropertyExpression role : tmp) {
            if (!role.isDataPropertyExpression()) {
                OWLPropertyExpression inv = ((OWLObjectPropertyExpression) role).getInverseProperty();
                rolesPinv.add(inv);
                RoleAttributes attr = null;
                if (data.getObjectPropWithAttr().get(role).isTransitive()) {
                    attr = new RoleAttributes(false, false, true, false, false);
                } else {
                    attr = new RoleAttributes(false, false, false, false, false);
                }
                data.getObjectPropWithAttr().put((OWLObjectPropertyExpression) inv, attr);
            }
        }
        //build closure of P- where P is an object property
        for (OWLPropertyExpression role : rolesPinv) {
            if (!rolesInHierarchy.contains(role)) {
                Set<OWLPropertyExpression> rs = new HashSet<>();
                rs.add(role);
                data.getSubClosureByRole().putAll(role, rs);
                rs = new HashSet<>();
                rs.add(role);
                data.getSuperClosureByRole().putAll(role, rs);
            }
        }
        this.computeRoleClosure(data.getSuperClosureByRole());
        this.computeRoleClosure(data.getSubClosureByRole());
    }

    /*
     * Adds all roles S if role <= S transitively
     * Adds all roles S- if role- <= S transitively since role- <= S implies role <= S-
     */
    public void computeRoleClosure(SetMultimap<OWLPropertyExpression, OWLPropertyExpression> init) {
        boolean nstop = true;
        while (nstop) {
            nstop = false;
            //each r and r- is considered
            for (OWLPropertyExpression r : init.keySet()) {
                Set<OWLPropertyExpression> rs = new HashSet<>(init.get(r));
                for (OWLPropertyExpression r1 : rs) {
                    if (init.get(r).addAll(init.get(r1)))
                        nstop = true;
                    if (r instanceof OWLObjectPropertyExpression &&
                            init.get(((OWLObjectPropertyExpression) r).getInverseProperty())
                                    .addAll(init.get(((OWLObjectPropertyExpression) r1).getInverseProperty())))
                        nstop = true;
                }
            }
        }
    }

    public ReasoningData getData() {
        return data;
    }
}
