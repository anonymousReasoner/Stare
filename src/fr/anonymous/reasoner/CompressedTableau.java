package fr.anonymous.reasoner;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;
import org.semanticweb.owlapi.model.*;
import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;
import org.semanticweb.owlapi.model.OWLIndividual;
import java.util.*;
import java.util.concurrent.CopyOnWriteArraySet;


public class CompressedTableau {
	public int id=0;
    private CopyOnWriteArraySet<Layer> Slayer;
    private static OWLDataFactory factory = new OWLDataFactoryImpl();

    public static void init(OWLOntology ontology, ReasoningData rd, PrefixManager pmanager, CompressedTableau ct, MatchingFn mf) {
        List<OWLIndividual> inds = new ArrayList<OWLIndividual>();
        ConceptLabel indLabel = new ConceptLabel();
        inds = rd.getABox().getInitInds();
        ABox a = rd.getABox();
        
        a.addIndividuals(inds);

        a.setInitInds(inds);

        rd.setInitCore(indLabel);
        Layer l_0 = new Layer();
        l_0.setNominal(true);
        CopyOnWriteArraySet<Startype> Sst = new CopyOnWriteArraySet<Startype>();
        // creation of star-types and neighbourhood relation ship maintaining
        for (OWLIndividual ind : inds) {

            Set<OWLIndividual> closure = new HashSet<>();
                    //ind.getSameIndividuals(ontology);
            closure.add(ind);
            Startype st = rd.createInitStartype(closure);
            
            st.getCore().setIndividual(closure);
            Set<OWLClassExpression> concepts = rd.getConceptsFromPrimitiveAxioms( st.getCore().getConcepts(), new HashSet<OWLClassExpression>());
           // System.out.println("init "+concepts);
           
            st.setAddress(l_0);
            SetMultimap<OWLIndividual, OWLClassExpression> conceptsbyind = a.getConceptsByInd();
            //System.out.println(a.getConceptsByInd());
            a.setConceptsByInd(conceptsbyind);
            st.setNominal(true);
            st.setSaturated(false);
            rd.neighbourhood(st, ontology, a, pmanager);
            Sst.add(st);

            for (Triple t : st.getTriples()) {
                Omega o = new Omega(st, t);
                mf.getMatch().add(o);
            }

         
        }

        l_0.setSstar(Sst);
        CopyOnWriteArraySet<Layer> slayer = ct.getSlayer();
        slayer.add(l_0);
        ct.setSlayer(slayer);
        //initializing the matching fn
        for (Startype s : l_0.getSstar()) {
            for (Triple t : s.getTriples()) {
                //individuals
                if (!(t.getRay().getTip().getIndividual() == null) && !(t.getRay().getTip().getIndividual().isEmpty())) {

                    for (Startype o : l_0.getSstar()) {

                        if (t.getRay().getTip().getIndividual().equals(o.getCore().getIndividual())) {

                            if (mf.getMatch() != null) {
                                for (Omega c : mf.getMatch()) {

                                    //add o to omega(s,t)
                                    if (c.getS().equals(s)) {


                                        if (c.getT().equals(t)) {
                                            c.getSset().add(o);
                                            //System.out.println("star-type "+s.getCore().getIndividual()+" is match with "+o.getCore().getIndividual()+" through the triple "+t.getRay().getTip().getIndividual());                  
                                        }

                                    }
                                }
                            }
                        }
                    }
                }

            }
        }
        System.out.println("\nIn the initialization step we have created " + l_0.getSstar().size() + " star-types:\n");
        System.out.println("\n\n----------------------------------------------------------------");
        System.out.println("----------------------------Initialization----------------------");
        System.out.println("----------------------------------------------------------------");
        System.out.println();
        for (Startype s : l_0.getSstar()) {
       
            System.out.println(s.getCore().toString( ) );
         //   System.out.println(s.getTriples().size());
        }
        System.out.println();
        System.out.println("----------------------------Initialization----------------------");
        System.out.println("----------------------------------------------------------------");
        System.out.println("----------------------------------------------------------------\n\n");


    }

    public static void mainAlgo(Startype star, Layer layer, CompressedTableau ct, ReasoningData rd, MatchingFn mf, OWLOntology ontology) {
    	System.out.println( star.getCore().toString());
        Set<Startype> addedSetOfStartype = new HashSet<>();


        ListIterator<OWLClassExpression> Iterator_concepts = new ArrayList<>(star.getCore().getConcepts()).listIterator();
        while (Iterator_concepts.hasNext()) {
            System.out.println("-----------------Concept---------------------");

            OWLClassExpression cl = Iterator_concepts.next();
            SetMultimap<Triple, Triple> his = HashMultimap.create(50, 50);

            //System.out.println("The concept is: "+cl);
            // add this subset thing to the saturation function
            //for(OWLClassExpression cl:st.getCore().getConcepts()) {
            // System.out.println("Is subset rule applicable:"+ cl.getClassesInSignature());
            //	 }

            boolean inter = star.isIntersectionRule(cl, rd);
            System.out.println("Is intersection rule applicable:" + inter);
            if (inter) {
            	 System.out.println("inter "+cl);
                Startype star_derived = star.intersectionRule(star, cl, his, rd);
                if (star_derived.isCoreValid(star_derived.getCore().getConcepts(), rd) && star_derived.isCoreValidInd(star_derived, ontology)) {
                    star_derived.setParent(star);
                    star_derived.setAddress(star.getAddress());
                    
                    star_derived.getAddress().getSstar().add(star_derived);
               //     System.out.println(star_derived.getCore().toString());
                    if (star_derived.getAddress().isNominal()) {
                        star_derived.setNominal(true);
                    }
                    mf.matchingPred(star_derived, star_derived.getParent(), star_derived.getAddress(), ct, mf, rd);
              
                }
                
                
                else {
                	System.out.println("not valid");
                }
            }


            boolean exists = star.isSomeRule(cl, rd, layer, ct);

            System.out.println("Is existential rule applicable:" + exists);

            if (exists) {
System.out.println(cl);
                Startype star_derived = star.stsomeRule(star, cl, his, rd, mf, ct, ontology);
                star_derived.setParent(star);
                star_derived.setAddress(star.getAddress());
                if (star_derived.isCoreValid(star_derived.getCore().getConcepts(), rd) && star_derived.isCoreValidInd(star_derived, ontology)) {
                    star_derived.setParent(star);
                    star_derived.setAddress(star.getAddress());
                    star_derived.getAddress().getSstar().add(star_derived);
                   // mf.matchingPred(star_derived, star_derived.getParent(), star_derived.getAddress(), ct, mf, rd);

                    if (star_derived.getAddress().isNominal()) 
                        star_derived.setNominal(true);
                    


                }


            }

            boolean all = star.isAllRule(cl, rd);
            System.out.println("Is for-all rule applicable:" + all);
            if (all) {
                Startype star_derived = star.stAllRule(cl, his, rd, mf, ct, ontology); 
                star_derived.setParent(star);
                star_derived.setAddress(star.getAddress());
                star_derived.getAddress().getSstar().add(star_derived);
              //  mf.matchingPred(star_derived, star_derived.getParent(), star_derived.getAddress(), ct, mf, rd);
            }
								

            boolean union = star.isUnionRule(cl, rd);
            System.out.println("Is union rule applicable:" + union);
            if (union) {
            	 System.out.println("union "+cl);
                Set<Startype> s_nonDetDerived = star.unionRule_new(star, cl, his, rd);


                for (Startype st : s_nonDetDerived) {
                    if (st.isCoreValid(st.getCore().getConcepts(), rd) && st.isCoreValidInd(st, ontology)) {
                    
                        st.setParent(star);
                        st.setAddress(star.getAddress());
                        st.getAddress().getSstar().add(st);
                      /*  if (st.getAddress().isNominal()) {
                            st.setNominal(true);
                        }*/
                        System.out.println("union derived "+ st.getCore().toString());
//
                        mf.matchingPred(st, star, star.getAddress(), ct, mf, rd);
//
                        
                    /*    for(Triple t_new:st.getTriples()) {
                        	 for(Triple t_old:st.getTriples()) {
                        		 if(t_new.getRay().equals(t_old.getRay()))
                        	mf.matchTriple(st, t_new, star, t_old, st.getAddress(), ct, mf, rd);
                        	 }
                        }*/
  
                    }
                }
            }


        }
        System.out.println("-------------------------------------------------");
       

    }

    public static void saturateALC(Startype star, Layer layer, CompressedTableau ct, ReasoningData rd, MatchingFn mf, OWLOntology ontology) {

        mainAlgo(star, layer, ct, rd, mf, ontology);


    }


    public static Set<Startype> link(Startype s_1, Startype s_2, ReasoningData rd, MatchingFn mf, CompressedTableau ct, OWLOntology ontology) {


        Set<Startype> addedSetOfStartype = new HashSet<>();

        LinkkeyRules lkr = new LinkkeyRules();
       
        if (s_1.isNominalValid(s_1.getCore().getIndividual(), rd) && s_2.isNominalValid(s_2.getCore().getIndividual(), rd)) {

if(rd.getLKBox().getLks()!=null) {
            for (Linkey lk : rd.getLKBox().getLks()) {


                if (!s_1.equals(s_2)) {
                    StartypePair p = new StartypePair(s_1, s_2);
                  
                    Startype starPair_1 = lkr.chlk_1Rule(s_1, s_2, rd, lk, mf);
                   
                    if (starPair_1 != null && !(starPair_1.equals(s_1)) && starPair_1.isValid(starPair_1.getCore(), rd)) {
                    	//System.out.println("We have applied chLK_1 rule: "+s_1.getCore().toString()+" and "+s_2.getCore().toString());
                     
                        starPair_1.setParents(p);
                        starPair_1.setAddress(s_1.getAddress());
                        s_1.getAddress().getSstar().add(starPair_1);
                        mf.matchingPred(starPair_1, s_1, s_1.getAddress(), ct, mf, rd);


                    }


                    Startype starPair_2 = lkr.chlk_2Rule(s_1, s_2, rd, lk, mf);
                   

                    if (starPair_2 != null && !(starPair_2.equals(s_1)) && starPair_2.isValid(starPair_2.getCore(), rd)) {
                    	//System.out.println("we have applied chLK_2 rule: "+s_1.getCore().toString()+" and "+s_2.getCore().toString()+" through the link key"+lk.getPairsOfConcepts().getFirstConcept().toString()+" and "+lk.getPairsOfConcepts().getSecondConcept().toString());
                    
                    	starPair_2.setParents(p);
                        starPair_2.setAddress(s_2.getAddress());
                        s_1.getAddress().getSstar().add(starPair_2);
                        mf.matchingPred(starPair_2, s_2, s_1.getAddress(), ct, mf, rd);

                    }

                  if(  lkr.lkRule(s_1, s_2, rd, lk, mf)) {
                	  
                	  Startype merge = lkr.merge(s_1, s_2, rd);
                      //check the validity for equality
                
                      if (!s_1.getAddress().getSstar().contains(merge)&&merge.isValid(merge.getCore(), rd) && merge.isNominalValid(merge.getCore().getIndividual(), rd)&&!lkr.isMergeContained(s_1, s_2)) {
                    	//  System.out.println("we have applied LK rule on: "+s_1.getCore().toString()+" and "+s_2.getCore().toString());
                    	  merge.setParents(p);
                          merge.setAddress(s_1.getAddress());
                          if( ! s_1.getAddress().getSstar().contains(merge)) {
                          s_1.getAddress().getSstar().add(merge);
                          mf.matchingMerge(s_1, s_2, merge, ct, mf, rd);
                          }
                	  
                  }
                  }
                    if (lkr.shouldMerge(s_1, s_2, rd,mf)) {
                        Startype merge = lkr.merge(s_1, s_2, rd);
                        //check the validity for equality
                    
        
                        if (merge.isValid(merge.getCore(), rd) && merge.isNominalValid(merge.getCore().getIndividual(), rd)&&lkr.isMergeContained(s_1, s_2)) {
                        //	System.out.println("We have applied equality rule: "+s_1.getCore().toString()+" and "+s_2.getCore().toString());
                            merge.setParents(p);
                            merge.setAddress(s_1.getAddress());
                            if( ! s_1.getAddress().getSstar().contains(merge)) {
                            s_1.getAddress().getSstar().add(merge);
                            mf.matchingMerge(s_1, s_2, merge, ct, mf, rd);
                            }
                         
                        }


                    }
                }
                else {
                    // System.out.println("I contain a clash and could not be added");
                }

            }
        }
        }


        return addedSetOfStartype;
    }

    public static Set<Startype> saturateLK(Startype s_1, Startype s_2, Layer layer, CompressedTableau ct, ReasoningData rd, MatchingFn mf, OWLOntology ontology) {
        Set<Startype> addedSet_lk = new HashSet<Startype>();
        link(s_1, s_2, rd, mf, ct, ontology);


        return addedSet_lk;


    }

    public static 	CopyOnWriteArraySet<Layer> align(Layer layer, Set<OWLIndividual> set, ReasoningData rd, CompressedTableau ct){
    	CopyOnWriteArraySet<Layer > set_all = new CopyOnWriteArraySet<Layer>();
    	for (OWLIndividual ind : set) {

    	Layer set_ind=new Layer();
        for (Startype st : layer.getSstar()) {
        	
        
            if (st.isSaturated(layer, rd, ct) && st.getCore().getIndividual().contains(ind)) {

       set_ind.getSstar().add(st);
            	
            }
        

        }
      

     
        set_all.add(set_ind);
    }
    	
    	
    	return set_all;
    }
    public static Set<Layer> generateSubsets(Layer layer, Set<Layer> set, ReasoningData rd, CompressedTableau ct) {
      Set<Layer> choices=new HashSet<Layer>();
     
    	//CopyOnWriteArraySet<Layer > set_all = new CopyOnWriteArraySet<Layer>();
        Layer l = new Layer();
       
       // set_all=align(layer, set, rd, ct);
        if(set.size()==1) {
        	
        	for(Layer l_1:set) {
        		for(Startype s: l_1.getSstar()) {
        			Layer l_=new Layer();
        			l_.getSstar().add(s);
        			choices.add(l_);
        		}
        	}
        	return choices;
        }
        else {
      
       	for(Layer l_other:set) {
           		for(Startype s: l_other.getSstar()) {
    
        				set.remove(l_other);
          		
          			
               			// for(Layer ll:generateSubsets(layer, set, rd, ct)) {
               				//Layer l_=new Layer();
                  			 
                  			for(Layer ll:generateSubsets(layer, set, rd, ct)) {
                  		//	 ll.getSstar().addAll(l_.getSstar());
                  				//l_.getSstar().add(s);
                  				ll.getSstar().add(s);
                  			  choices.add(ll);  
                  			  
               			 }
         			         			
       		}
           
         		}
       	
       	
        	}
        



        return choices;
    }

    public static boolean singleCheck(Startype st, Layer l, MatchingFn mf, ReasoningData rd, CompressedTableau ct) {

        boolean validchoice = true;
      

            for (Triple t : st.getTriples()) {

                if (t.getRay().getTip().getConcepts()!=null) {

                    for (Omega o : mf.getMatch()) {

                        if (o.getS().equals(st)) {

                            if (o.getT().equals(t)) {
                                if (!o.getSset().isEmpty()) {
                                	if(o.getSset()!=null)
                                    for (Startype w : o.getSset()) {

                                        
                                        if (w.isSaturated(w.getAddress(), rd, ct)) {

                                            validchoice = true;

                                            validchoice = singleCheck(w, w.getAddress(), mf, rd, ct);


                                        }
                                       
                                        else {

                                            validchoice = false;
                                        }
                                    }
                                	else {
                                		 validchoice = false;
                                	}


                                } else {

                                    validchoice = false;
                                }


                            }// checking the index
                        }//accessing the matching function
                    }//all triples
                }// all st in the layer
        }//all layers in ct

        return validchoice;

    }

    

    public static boolean checkNew(CompressedTableau ct, MatchingFn mf, ReasoningData rd) {


    	Layer nominal=null;
    	boolean matched=false;
    	
		for(Layer layer:ct.getSlayer()) {
			
    		if(layer.isNominal()) {
    			Set<Layer> set_all=align(layer, rd.getABox().getInds(), rd, ct);
    			Set<Layer> layers=generateSubsets(layer, set_all, rd, ct);
    		//	System.out.println(layers.size());
    			Iterator<Layer> it = layers.iterator();
    			while(it.hasNext()) {
    				
    			nominal=it.next();
    		/*	  for(Startype star:nominal.getSstar()) {
    		        	System.out.println(star.getCore().getIndividual());
    		        }*/
    			
    			if(nominal.satisfyLkandEqualities(rd, mf)) {
    	
    	        
            	
            	for(OWLIndividual ind:rd.getABox().getInds()) {
            
            	
                    for (Startype st : nominal.getSstar()) {
                		
                    if(st.getCore().getIndividual().contains(ind)) {
                    	
            
                    if (singleCheck(st, nominal.next(ct, nominal), mf, rd, ct)) {
                     
                    	 matched=true;
                    }
                    
            	
            }
            
                   }
                
                  
                   }
    			}
            	/*else {
            		System.out.println("I don't satisfy LKs");
            	}*/
    			

    				}
    			}
		}
        
    
        return matched;


    }

    //chooseLK not correctly implemented
    public static boolean main(CompressedTableau ct, MatchingFn mf, OWLOntology ontology, ReasoningData rd) {
       // CopyOnWriteArraySet<Layer> layers = ct.getSlayer();
       boolean changed=true;
       LinkkeyRules lkr=new LinkkeyRules();
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
        Set<Startype> processed = new HashSet<Startype>();
        Set<Startype> addedSet = new HashSet<Startype>();
        Set<Startype> addedSetLk = new HashSet<Startype>();
        Set<StartypePair> processed_LK = new HashSet<StartypePair>();


       
        System.out.println("The reasoner checking if your ontology is consistent.....\n\n");

        System.out.println("\n\n So we first saturate each star-type built in the initialization step: \n\n");

     //   for (int i = 0; i < ct.getSlayer().size(); i++) {
        while(changed) {
        	changed=false;

        ListIterator<Layer> layers_iterator = new ArrayList<Layer>(ct.getSlayer()).listIterator();
while(layers_iterator.hasNext()) {

            Layer l = layers_iterator.next();
            ListIterator<Startype> star_iterator = new ArrayList<Startype>(l.getSstar()).listIterator();
     //there is a pb in the loop here
            //     for (int j = 0; j < l.getSstar().size(); j++) {
           
            while( star_iterator.hasNext()) {
                Startype st = star_iterator.next();
        

        
               // System.out.println( st.getCore().toString());
                if (!processed.contains(st) && !st.isSaturated(l, rd, ct) && !l.isBlocked(st, ct, l)) {
                    System.out.println("*******************************************");
                    System.out.println("*******************************************\n\n");
                	changed=true;
                    System.out.println("\nThis star-type is not processed and not saturated.\n");

                    processed.add(st);
                    saturateALC(st, l, ct, rd, mf, ontology);


               
            
                
            } else if (processed.contains(st)) {
                System.out.println("\nI'm already processed.\n");
            } else if (st.isSaturated(l, rd, ct)) {
                System.out.println("\nI'm saturated so there is no ALC rule applicable on me.\n");
            } else if (l.isBlocked(st, ct, l)) {
                System.out.println("I'm blocked");
            }
            }
                System.out.println("\nLet us now check LK rules by first traversing each pair of star-type in the first layer \n");
               if (l.isNominal()) {
           	
                    for (Startype s_1 : l.getSstar()) {
                        for (Startype s_2 : l.getSstar()) {
                        	
                        	  StartypePair p = new StartypePair(s_1, s_2);
                        	  boolean contained=false;
                        	  for(StartypePair pp:processed_LK) {
                        	 if(pp.getFirstStar().equals(s_1) &&pp.getSecondStar().equals(s_2)) {
                        		  contained = true;
                        	 }
                        	  }
                        	  if(!contained&&lkr.isLkRuleApp(s_1, s_2,rd.getLKBox() , mf, rd)) {
                     // 
                        		 // System.out.print("here");
                            	saturateLK(s_1, s_2, l, ct, rd, mf, ontology);
                            
                            	changed=true;
                        		  
                        	  
                        	
                        	 
                        	  }
                        	  processed_LK.add(p);
                        	//  System.out.println("after pLK "+ processed_LK.contains(p));
                              //System.out.println("after appl. "+ lkr.isLkRuleApp(s_1, s_2,rd.getLKBox() , mf, rd));
                        }
                        
                        }
                    }
               
               
}

/*if(checkNew(ct, mf, rd) ) {

	return true;
}*/
        }
                



        return false;
    }




    public CopyOnWriteArraySet<Layer> getSlayer() {
        return Slayer;
    }


    public void setSlayer(CopyOnWriteArraySet<Layer> slayer) {
        Slayer = slayer;
    }
}
