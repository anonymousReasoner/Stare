package fr.anonymous.reasoner;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.model.OWLIndividual;

import java.util.*;
import java.util.concurrent.CopyOnWriteArraySet;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.stream.Collectors;


public class CompressedTableau {
    final static Logger logger = Logger.getLogger(String.valueOf(CompressedTableau.class));
    public static final int id = 0;
    private static int idGlobal = 0;
    private CopyOnWriteArraySet<Layer> Slayer;

    public static void initMf(Layer l) {

        for (Startype s : l.getSstar()) {
            for (Triple t : s.getTriples()) {
                Succ sc = new Succ();
                sc.setT(t);
                s.getSucc().getMatch().add(sc);
                Set<Startype> matched = l.getSstar().stream().filter(o -> o.getCore().equals(t.getRay().getTip())).collect(Collectors.toSet());
                for (Startype o : matched) {
                    //Set<Succ> toAdd = o.getSucc().getMatch().stream().filter(c -> ( c.getT().equals(t))).collect(Collectors.toSet());
                    sc.getSset().add(o);
                }
            }
        }
    }

    public static void init(OWLOntology ontology, ReasoningData rd, PrefixManager pmanager, CompressedTableau ct) {

        ConceptLabel indLabel = new ConceptLabel();
        ABox a = rd.getABox();
        List<OWLIndividual> inds = a.getInitInds();

        rd.setInitCore(indLabel);
        Layer l = new Layer(true);
        l.setId(1);
        CopyOnWriteArraySet<Startype> Sst = new CopyOnWriteArraySet<>();

        l.setSstar(Sst);
        ArrayList<Startype> set = new ArrayList<>();
        // creation of star-types and neighbourhood relation ship maintaining
        for (OWLIndividual ind : inds) {

            Set<OWLIndividual> closure = new HashSet<>();
            closure.add(ind);
            Startype st = rd.createInitStartype(ontology, closure);
            st.getCore().setIndividual(closure);
            st.setAddress(l);
            st.setNominal(true);
            idGlobal++;
            //st.setIdS(idGlobal);
            st.setSucc(new Match());
            l.getSstar().add(st);
            rd.neighbourhood(st, a, pmanager);

            for (Triple t : st.getTriples()) {
                Succ o = new Succ();
                o.setT(t);
                st.getSucc().getMatch().add(o);
            }
        }
        //
        CopyOnWriteArraySet<Layer> slayer = ct.getSlayer();
        slayer.add(l);
        ct.setSlayer(slayer);
        //initializing the matching fn
        initMf(l);

        logger.log(Level.FINE, "\nIn the initialization step we have created " + l.getSstar().size() + " star-types:\n");

        System.out.println("\n\n----------------------------------------------------------------");
        System.out.println("----------------------------Initialization----------------------");
        System.out.println("----------------------------------------------------------------");
        System.out.println();
        for (Startype s : l.getSstar()) {
            System.out.println();
            System.out.println(s.getCore().getIndividual().toString() + " and I have " + s.getTriples().size() + " triples.");
        }
        System.out.println();
        System.out.println("----------------------------Initialization----------------------");
        System.out.println("----------------------------------------------------------------");
        System.out.println("----------------------------------------------------------------\n\n");
    }

    public static void saturateALC(Startype star, CompressedTableau ct, ReasoningData rd, OWLOntology ontology, OWLDataFactory data) {
        System.out.println(star.getCore().toString());
        System.out.println(star.getCore().getIndividual());
        ListIterator<OWLClassExpression> Iterator_concepts = new ArrayList<>(star.getCore().getConcepts()).listIterator();

        while (Iterator_concepts.hasNext()) {
            System.out.println("-----------------Concept---------------------");

            OWLClassExpression cl = Iterator_concepts.next();
            // SetMultimap<Triple, Triple> his = HashMultimap.create(50, 50);


            System.out.println(cl);

            Startype star_derivedI = star.intersectionRule(star, cl, rd);
            if (star_derivedI != null) {

                System.out.println("Intersection Applied");
                if (star_derivedI.isCoreValid(star_derivedI.getCore().getConcepts(), rd) && star_derivedI.isCoreValidInd(star_derivedI, ontology)) {
                    System.out.println("Intersection Applied and valid");
                    idGlobal++;
                    //;
                    //  star_derivedI.setIdS(idGlobal);
                    star_derivedI.setParent(star);
                    star_derivedI.setAddress(star.getAddress());
                    star_derivedI.getAddress().getSstar().add(star_derivedI);
                    star_derivedI.setNominal(star_derivedI.getAddress().isNominal());
                    star.getSucc().matchingCore(star_derivedI.getParent(), star_derivedI, rd, ct);
                    //   System.out.println(star_derivedI.getCore().getIndividual());

                } else {

                    System.out.println("not valid after intersection rule");
                }
            }

            Startype star_derivedA = star.stAllRule(cl, rd, ct, ontology, data);
            if (star_derivedA != null) {
                System.out.println("All Applied");
                if (star_derivedA.isCoreValid(star_derivedA.getCore().getConcepts(), rd) && star_derivedA.isCoreValidInd(star_derivedA, ontology)) {
                    idGlobal++;
                    //star_derivedA.setIdS(idGlobal);
                    //System.out.println(idGlobal);
                    star_derivedA.setParent(star);
                    star_derivedA.setAddress(star.getAddress());
                    star_derivedA.setNominal(star_derivedA.getAddress().isNominal());
                    star_derivedA.getAddress().getSstar().add(star_derivedA);
                    // System.out.println(star_derivedA.getCore().getIndividual());
                } else {
                    System.out.println("not valid after all rule");

                }
            }
            Set<Startype> s_nonDetDerived = star.unionRule_new(star, cl, rd, ct, ontology);
            if (s_nonDetDerived != null)
                System.out.println("Union Applied");
            else
                System.out.println("not valid after union rule");


            Startype star_derivedSt = star.stsomeRule(star, cl, rd, ct, ontology, data);
            if (star_derivedSt != null)
                System.out.println("exists rule applied ");

            else
                System.out.println("not valid after exists rule");


            Startype star_derivedS = star.sub(star, rd, ontology, ct);
            if (star_derivedS != null) {

                System.out.println("GCI Applied");
                if (star_derivedS.isCoreValid(star_derivedS.getCore().getConcepts(), rd) && star_derivedS.isCoreValidInd(star_derivedS, ontology)) {
                    System.out.println("GCI Applied and valid");
                    idGlobal++;
                    //;
                    //  star_derivedI.setIdS(idGlobal);
                    star_derivedS.setParent(star);
                    star_derivedS.setAddress(star.getAddress());
                    star_derivedS.getAddress().getSstar().add(star_derivedS);
                    star_derivedS.setNominal(star_derivedS.getAddress().isNominal());
                    star.getSucc().matchingCore(star_derivedS.getParent(), star_derivedS, rd, ct);
                    //   System.out.println(star_derivedI.getCore().getIndividual());

                } else {

                    System.out.println("not valid after GCI rule");
                }
            }

            System.out.println("-------------------------------------------------");

        }

    }


    public static void merge(Startype s_1, Startype s_2, ReasoningData rd, CompressedTableau ct) {

        LinkkeyRules lkr = new LinkkeyRules();
        StartypePair p = new StartypePair(s_1, s_2);
        if (rd.getLKBox() != null) {
            for (Linkey lk : rd.getLKBox().getLks()) {

                if (lk.lkRule(s_1, s_2, lk)) {

                    Set<Startype> merges = lk.merge(s_1, s_2, rd);
                    for (Startype merge : merges) {

                        if (merge.isValid(merge.getCore(), rd) && merge.isNominalValid(merge.getCore().getIndividual(), rd) && !lk.isMergeContained(s_1, s_2)) {
                            System.out.println("the merge is valid");
                            merge.setParents(p);
                            merge.setAddress(s_1.getAddress());
                            s_1.getAddress().getSstar().add(merge);
                            //  mf.matchingMerge(s_1, s_2, merge,  mf, rd);
                        } else {
                            //
                            System.out.println("Not valid after merging");
                        }
                    }
                }
            }
            if (rd.getLKBox().getLks().iterator().next().shouldMerge(s_1, s_2, rd)) {
                Set<Startype> merges = rd.getLKBox().getLks().iterator().next().merge(s_1, s_2, rd);
                //check the validity for equality
                Set<Startype> m = merges.stream().filter(merge -> merge.isValid(merge.getCore(), rd) && merge.isNominalValid(merge.getCore().getIndividual(), rd) && rd.getLKBox().getLks().iterator().next().isMergeContained(s_1, s_2)).collect(Collectors.toSet());
                for (Startype merge : m) {
                    merge.setParents(p);
                    merge.setAddress(s_1.getAddress());
                    s_1.getAddress().getSstar().add(merge);
                    s_1.getSucc().matchMerge(s_1, s_2, merge, rd, ct);
                }
            }
        }
    }


    public static void saturateLK(Startype s_1, Startype s_2, ReasoningData rd, CompressedTableau ct) {
        // System.out.println("Inside saturate LK");
        // int i=0;
        if (rd.getLKBox() != null) {
            //System.out.println("The number of link keys is: "+rd.getLKBox().getLks().size());
            for (Linkey lk : rd.getLKBox().getLks()) {
                //  i++;
                // System.out.println("inside the lk loop of saturate lk"+i);
                StartypePair p = new StartypePair(s_1, s_2);
                Startype starPair_1 = lk.chlk_1Rule(s_1, s_2, rd, lk);
                if (starPair_1 != null && !starPair_1.equals(s_1) && starPair_1.isValid(starPair_1.getCore(), rd)) {
                    //  System.out.println("After chLK1");
                    starPair_1.setParents(p);
                    starPair_1.setAddress(s_1.getAddress());
                    s_1.getAddress().getSstar().add(starPair_1);
                    s_1.getSucc().matchingCore(s_1, starPair_1, rd, ct);
                }
                Startype starPair_2 = lk.chlk_2Rule(s_1, s_2, rd, lk);
                if (starPair_2 != null && !starPair_2.equals(s_1) && starPair_2.isValid(starPair_2.getCore(), rd)) {
                    //   System.out.println("After chLK2");
                    starPair_2.setParents(p);
                    starPair_2.setAddress(s_2.getAddress());
                    s_1.getAddress().getSstar().add(starPair_2);
                    s_2.getSucc().matchingCore(s_2, starPair_2, rd, ct);
                }
            }
            merge(s_1, s_2, rd, ct);
        }
    }


    public static CopyOnWriteArraySet<Layer> align(Layer layer, Set<OWLIndividual> set, ReasoningData rd, CompressedTableau ct, OWLOntology ontology) {
        CopyOnWriteArraySet<Layer> set_all = new CopyOnWriteArraySet<>();
        for (OWLIndividual ind : set) {
            Layer set_ind = new Layer();
            for (Startype st : layer.getSstar()) {
                if (st.isSaturated( rd, ontology) && st.getCore().getIndividual().contains(ind))
                    set_ind.getSstar().add(st);
            }
            set_all.add(set_ind);
        }
        return set_all;
    }

    public static ArrayList<ArrayList<Startype>> generateCorrepondances(Set<OWLIndividual> inds, Layer set, ReasoningData rd, CompressedTableau ct, OWLOntology ontology) {
        ArrayList<ArrayList<Startype>> correspondances = new ArrayList<>();
        for (OWLIndividual ind : inds) {
            ArrayList<Startype> indToStar = new ArrayList<>
                    (set.getSstar().stream().filter(a -> a.getCore().getIndividual().contains(ind) && a.isSaturated( rd,  ontology)).collect(Collectors.toSet()));
            correspondances.add(indToStar);
        }
        return correspondances;
    }

    public static ArrayList<Layer> generateSubsets(Set<OWLIndividual> inds, Layer set, ReasoningData rd, CompressedTableau ct, OWLOntology ontology) {
        ArrayList<ArrayList<Startype>> correspondances = generateCorrepondances(inds, set, rd, ct, ontology);
        ArrayList<Set<Startype>> allSubsets = new ArrayList<>();
        System.out.println("The number of the total correspondances built is: " + correspondances.size());
        for (ArrayList<Startype> corr : correspondances) {
            System.out.println("This correspondance contains: " + corr.size());
            for (Startype s : corr) {
                Set<Startype> newSubset = new HashSet<>();
                newSubset.add(s);
                allSubsets.add(newSubset);
            }
        }
        boolean modified = true;
        Set<Set<Startype>> proc = new HashSet<>();
        while (modified) {
            modified = false;
            //infinite loop here
            //  System.out.println("hereeee");
            ListIterator<Set<Startype>> iter_main = new ArrayList<Set<Startype>>(allSubsets).listIterator();
            while (iter_main.hasNext()) {
                Set<Startype> subset = iter_main.next();
                boolean present = false;
                if (!proc.contains(subset)) {
                    for (ArrayList<Startype> corr : correspondances) {
                        for (Startype s : subset) {

                            for (Startype c : corr) {
                                if (s.getCore().getIndividual().equals(c.getCore().getIndividual()) || s.getCore().getIndividual().containsAll(c.getCore().getIndividual()) || s.getCore().getIndividual().contains(c.getCore().getIndividual())) {
                                    present = true;

                                    break;
                                }
                            }
                            if (present) {

                                break;
                            }


                        }
                        if (present)
                            break;

                        // if we are already adding star-type with already contained individuals
                        if (!present) {

                            modified = true;
                            Iterator<Startype> iter_corr = corr.iterator();
                            while (iter_corr.hasNext()) {
                                Startype star_corr = iter_corr.next();
                                Set<Startype> moreSubset = new HashSet<>();
                                moreSubset.addAll(subset);
                                moreSubset.add(star_corr);
                                proc.add(subset);
                                allSubsets.add(moreSubset);
                            }
                        }
                    }
                } //
            }
        }
        boolean exists = false;
        Set<Set<Startype>> toremove = new HashSet<>();
        Iterator<Set<Startype>> iter = allSubsets.iterator();
        while (iter.hasNext()) {

            Set<Startype> subset = iter.next();
            for (OWLIndividual ind : inds) {
                exists = false;
                for (Startype s : subset) {
                    if (s.getCore().getIndividual().contains(ind) || s.getCore().getIndividual().equals(ind)) {
                        exists = true;
                    }
                }
                if (!exists) {
                    toremove.add(subset);
                }
            }
        }
        allSubsets.removeAll(toremove);
        Set<Set<Startype>> no_dup = new HashSet<>(allSubsets);
        ArrayList<Layer> allLayers = new ArrayList<>();
        for (Set<Startype> subset : no_dup) {

            Layer l = new Layer();
            l.setNominal(true);
            l.getSstar().addAll(subset);
            allLayers.add(l);
        }

        return allLayers;
    }

    public static boolean singleCheck(Startype st, ReasoningData rd, CompressedTableau ct, Layer l, OWLOntology ontology) {
        boolean validchoice = true;
        boolean found=false;

        if (st.isSaturated( rd,  ontology)) {

            for (Triple t : st.getTriples()) {
                //   System.out.println("Inside single check");
                if (t.getRay().getTip().getConcepts().isEmpty()||t.getRay().getTip().getConcepts()==null) {
                    //  System.out.println("The triple is dummy");
                    validchoice = true;
                    //  return validchoice;
                }
                else {

                    for (Succ o : st.getSucc().getMatch()) {


                        if (o.getT().equals(t)) {
                            for (Startype w : o.getSset()) {
                                if (w.isSaturated(rd, ontology)) {
                                    //System.out.println(w.isSaturated(w.getAddress(), rd, ct));
                                    if (singleCheck(w, rd, ct, l, ontology))
                                            found= true;
                                       // validchoice = false;


                                }
                            }
                        }
                    }
                }
            }
        }
        if(found=true)
            return true;
    
    


        return validchoice;
    }

    public static Set<Set<Startype>> sub(ReasoningData rd, CompressedTableau ct, OWLOntology ontology, LinkkeyRules lkr) {
        Set<Set<Startype>> sub = new HashSet<>();
        Layer first = ct.getSlayer().iterator().next();
        int n = first.getSstar().size();
        int nbr = 0, nbrs=1;
        boolean present = false;
        boolean contained = false;
        int k = 0;
        List<Startype> firstL = new ArrayList<>(first.getSstar());
        Iterator<Startype> f=firstL.listIterator();
        for (OWLIndividual ind : rd.getABox().getInitInds()) {
            nbr = 0;
            for (Startype st : firstL) {
                if (st.getCore().getIndividual().contains(ind)) {
                    nbr++;
                }
            }
                if (nbr == 0) {
                    return sub;
                }
                if(nbr>1){
                    nbr++;
                }
            }

           if(nbrs==1) {

            Set<Startype> s = new HashSet<>();
            s.addAll(firstL);
            sub.add(s);
return sub;
        }



                for (int i = 0; i < n; i++) {
                    k++;

                    Set<Startype> s = new HashSet<>();
                    // Print current subset
                    System.out.print(" Building the " + k + " subset");
                    if (firstL.get(i).isSaturated( rd,  ontology)) {
                        //  System.out.println("the star-type i while building the subsets" + firstL.get(i).getCore().getIndividual());
                        s.add(firstL.get(i));
                    }
                    for (int j = 0; j < n; j++) {
                        contained = false;


                        for (Startype r : s) {
                            if (r.getCore().getIndividual().equals(firstL.get(j).getCore().getIndividual())) {
                                //   System.out.println(r.getCore().getIndividual() +" and "+ firstL.get(j).getCore().getIndividual());
                                contained = true;
                            }
                        }
                        if (!contained) {

                            if (firstL.get(j).isSaturated( rd, ontology) && !s.contains(firstL.get(j))) {
                                // System.out.println("the star-type j while building the subsets" + firstL.get(j).getCore().getIndividual());
                                s.add(firstL.get(j));
                            }

                        }

                        //   System.out.println(firstL.get(j).isSaturated());

                    }


                    for (OWLIndividual ind1 : rd.getABox().getInitInds()) {
                        present = false;
                        for (Startype st : s) {
                            if (st.getCore().getIndividual().contains(ind1)) {
                                present = true;
                            }
                        }

                    }
                    if (present) {
                        //System.out.println("I have added one subset");
                        sub.add(s);
                    } else {
                        // System.out.println("subset not added");
                    }

                }

               // return sub;




        return sub;
    }

    public static boolean checkNew(CompressedTableau ct, ReasoningData rd, boolean lk, Layer layer, OWLOntology ontology, LinkkeyRules lkr) {

        boolean matched = false;
       // Layer l = new Layer();
        CopyOnWriteArraySet cs = new CopyOnWriteArraySet();
//for (Set<Startype> s: sub(rd, ct,ontology,lkr)) {


   // cs.addAll(s);
  //  l.setSstar(cs);
    Layer  l= ct.getSlayer().iterator().next();
    if (lk) {
        if (l.satisfyLkandEqualities(rd)) {
            for (Startype st : layer.getSstar()) {
                if (singleCheck(st, rd, ct, layer, ontology)) {
                    //    System.out.println("Inside single check"+singleCheck(st, rd, ct, layer, ontology));

                    matched = true;
                }
            }
        } else {
            System.out.println("I don't satisfy LKs");
        }
        if (matched==true)
                     return matched;

    } else {


        for (Startype st : layer.getSstar()) {
            if (singleCheck(st, rd, ct, layer, ontology)) {
                matched = true;
            }
        }
        if (matched == true) {
        }
        return matched;
    }



        return matched;
    }

    public static void main(CompressedTableau ct,  OWLOntology ontology, ReasoningData rd, boolean lk,  OWLDataFactory data) {

        boolean changed = true;
        //This is a simple solution for the underlying problem of your first code:
        //A ConcurrentModificationException is thrown
        //because you iterate through the list and removing from it at the same time.
        //Creates a copy of the original list,
        //which requires memory and an operation which performance depends
        //on the type of the list (ArrayList, LinkedList, etc.)
        //Additionally, nums.remove(value) is a 𝑂(𝑛) operation. Making this loop overall 𝑂(𝑛2)
        //If you want to "add" this approach would also work,
        //but I would assume you would iterate over a different collection
        //to determine what elements you want to add
        //to a second collection and then issue an addAll method at the end.
        //directly saturate the added set
        //recursivity
        //we saturate, then we add the star-types
        //if we implement the rule directly like there would be a current modification exception as well

        List<Startype> processed = new ArrayList<>();
        Set<Set<Startype>> processed_LK = new HashSet<>();
        System.out.println("The reasoner checking if your ontology is consistent.....\n\n");
        System.out.println("\n\n So we first saturate each star-type built in the initialization step: \n\n");
        while (changed) {
            changed = false;
            ListIterator<Layer> layers_iterator;
            layers_iterator= new ArrayList<Layer>(ct.getSlayer()).listIterator();
            while (layers_iterator.hasNext()) {
                Layer l = layers_iterator.next();
                ListIterator<Startype> star_iterator;
                star_iterator = new ArrayList<Startype>(l.getSstar()).listIterator();
                while (star_iterator.hasNext()) {

                    Startype st = star_iterator.next();

                   System.out.println("This startype of layer: "+ st.getAddress().getId() + "The number of layers in the ct: "+ct.getSlayer().size());




                    if (!processed.contains(st) && !st.isSaturated( rd, ontology)) {
                        changed = true;
                        System.out.println("*******************************************");
                        System.out.println("*******************************************\n\n");
                        System.out.println("\nThis star-type is not processed and not saturated.\n");
                        saturateALC(st, ct, rd, ontology, data);
                        processed.add(st);
                    } else if (processed.contains(st)) {
                        System.out.println("\nI'm already processed.\n");
                    } else if (st.isSaturated( rd, ontology)) {
                        System.out.println("\nI'm saturated so there is no ALC rule applicable on me.\n");
                    }
                }

                if (lk) {
                //    if(strategy.equals("all")) {
                        System.out.println("\nLet us now check LK rules by first traversing each pair of star-type in the first layer \n");
                        if (l.isNominal()) {
                            for (Startype s_1 : l.getSstar()) {
                                for (Startype s_2 : l.getSstar()) {
                                    Set<Startype> p = new HashSet<>();
                                    Set<StartypePair> pairs = new HashSet<>();
                                    LinkkeyRules lkr = new LinkkeyRules();
                                    Set<Set<Startype>> setOfLkApp = setOfPairLkApp(s_1, s_2, rd, rd.getLKBox());
                                    for (Set<Startype> s : setOfLkApp) {
                                        p.addAll(s);
                                    }
                                    // StartypePair pP = new StartypePair(s_1, s_2);
                                    if (!processed_LK.contains(p)) {
                                        changed = true;
                                        saturateLK(s_1, s_2, rd, ct);
                                        processed_LK.add(p);

                                    }

                                }
                            }
                        }
                        }

                    }

                }




           // return checkNew(ct,rd,lk,ct.getSlayer().iterator().next(),ontology);
        }

    private static Set<Set<Startype>> setOfPairLkApp(Startype s_1, Startype s_2, ReasoningData data, LKBox Lkbox) {
        Set<Set<Startype>> toReturn=new HashSet<>();
        List<Triple> triples_1=s_1.getTriples();
        List<Triple> triples_2=s_2.getTriples();
        LinkkeyRules lkr=new LinkkeyRules();
        if(Lkbox!=null) {

            
            if (data.getLKBox().getLks().iterator().next().shouldMerge(s_1, s_2, data)) {
                Set<Startype> set = new HashSet<>();
                set.add(s_1);
                set.add(s_2);
                toReturn.add(set);
            }
            for (Linkey lk : Lkbox.getLks()) {

                Set<PropertyPair> role = lk.getPropertySet();
                for (Triple tr_1 : triples_1) {
                    for (Triple tr_2 : triples_2) {
                        for (PropertyPair pp : role) {
                            if (pp.getFirstProperty() != null && pp.getSecondProperty() != null) {
                                for (Succ o1 : s_1.getSucc().getMatch().stream().filter(o -> o.getT().equals(tr_1) && tr_1.getRay().getRidge().getRoles().contains(pp.getFirstProperty())).collect(Collectors.toSet())) {
                                    for (Succ o2 : s_2.getSucc().getMatch().stream().filter(o -> o.getT().equals(tr_2) && tr_2.getRay().getRidge().getRoles().contains(pp.getSecondProperty())).collect(Collectors.toSet())) {
//System.out.println(o1.getT().getRay().getRidge().equals(tr_1.getRay().getRidge())&& o1.getT().getRay().getTip().equals(tr_1.getRay().getTip())&&tr_1.getRay().getRidge().getRoles().equals(pp.getFirstProperty()));
                                                if(o1.getSset().contains(o2.getSset())||o1.getSset().equals(o2.getSset())) {
                                                    Set<Startype> set = new HashSet<>();
                                                    set.add(s_1);
                                                    set.add(s_2);
                                                    set.addAll(o1.getSset());
                                                    toReturn.add(set);
                                                }
                                        }
                                }
                            }
                        }
                    }
                }
            }
        }
        return toReturn;
    }

    public CopyOnWriteArraySet<Layer> getSlayer() {
        return Slayer;
    }

    public void setSlayer(CopyOnWriteArraySet<Layer> slayer) {
        Slayer = slayer;
    }
}
