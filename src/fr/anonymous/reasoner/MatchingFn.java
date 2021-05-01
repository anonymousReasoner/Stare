package fr.anonymous.reasoner;



import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;
import java.util.concurrent.CopyOnWriteArrayList;

import org.semanticweb.owlapi.model.OWLClassExpression;

public class MatchingFn {
	CopyOnWriteArrayList<Omega> match;
	public MatchingFn(){
		this.match=new CopyOnWriteArrayList<Omega>();
	}

	public CopyOnWriteArrayList<Omega> getMatch() {
		return match;
	}

	public void setMatch(Set<Omega> match) {
		this.match = new CopyOnWriteArrayList<Omega>();
	}
//	st_1 is the derived star-type, st_2 is the original
	public  void matchingPred(Startype st_1, Startype st_2, Layer l,CompressedTableau ct, MatchingFn match, ReasoningData data ) {
	
		// I have to search for every predecessor of st_1 and create a copy of it

		Set<Startype> s=new HashSet<>();
		s.add(st_2);
		
				for(Omega c: match.getMatch()) {


					if(c.getSset().contains(st_2)||c.getSset().equals(s)) {
						{

							Triple t=c.getT();

							Startype pred_st_copy=new Startype();
							
							ConceptLabel cl= new ConceptLabel(c.getS().getCore().getConcepts(),c.getS().getCore().getIndividual());
							pred_st_copy.setCore(cl, data);

							List<Triple> trs=c.getS().getTriples();
							for(Triple tr:trs) {
								if(!tr.equals(t)) {
									pred_st_copy.getTriples().add(tr);
								}		
							}
							Triple t_new= new Triple();
							t_new.getRay().setRidge(t.getRay().getRidge());

							t_new.getRay().setTip(st_1.getCore());
							pred_st_copy.getTriples().add(t_new);
						//	System.out.println("Matched to a copy of the predecessor through the triple "+t_new.getRay().getTip().toString());
							
							Omega o=new Omega();
							o.setS(pred_st_copy);
							o.setT(t_new);
							o.getSset().add(st_1);
							match.getMatch().add(o);
							pred_st_copy.setAddress(c.getS().getAddress());
							c.getS().getAddress().getSstar().add(pred_st_copy);
						//now we have to add the successor of st_2 to pred_st_copy
							for(Triple tr_pred_copy: pred_st_copy.getTriples()) {
							 	for(Triple tr_pred:c.getS().getTriples()) {
							
								if(tr_pred_copy.getRay().equals(tr_pred.getRay())) {
									Omega m= new Omega();
								m.setS(pred_st_copy);
								m.setT(tr_pred_copy);
								for(Omega g:match.getMatch()) {
									if(g.getS().equals(c.getS())&&g.getT().equals(tr_pred)) {
										m.getSset().addAll(g.getSset());
									}
									
								}
								match.getMatch().add(m);
								
								}
							}
							
							}
							//then the predecessors 
						
								for(Omega g:match.getMatch()) {
									if(g.getSset().contains(c.getS())) {
										g.getSset().add(pred_st_copy);
									}
								}
					
							
						}
					}
				}

//				st_1 is the derived star-type, st_2 is the original
		
		//matching the successors of st_2 to st_1
		for(Triple t1:st_1.getTriples()) {
			for(Triple t2:st_2.getTriples()) {
				if(t1.getRay().equals(t2.getRay())) {
			for(Omega g:match.getMatch()) {
				if(g.getS().equals(st_2)&&g.getT().equals(t2)) {
					Omega g_=new Omega();
					g_.setS(st_1);
					g_.setT(t1);
					g_.setSset(g.getSset());
					match.getMatch().add(g_);
					
				}
			}
			}
		}
		}

	}
	public  void matchTriple(Startype st_1, Triple t_2,  Startype st_2, Triple t_1, Layer l,  CompressedTableau ct, MatchingFn match, ReasoningData rd) {


		Layer l_next=null;
		boolean matched=false;
	//matching to the successor
		
				for(Omega c: match.getMatch()) {

					if(c.getSset().contains(st_2)||c.getSset().equals(st_2)) {
						{
							
							c.getSset().add(st_1);
						//	System.out.println("Matched to the predecessor");
							
						}

					}
				}
		
			//for each unchanged triple
					for(Omega c: match.getMatch()) {
						if(c.getS().equals(st_2)){		
							for(Triple t:st_1.getTriples()) {
								if(c.getT().getRay().equals(t.getRay())) {
								Omega w=new Omega();
								w.setS(st_1);
								w.setT(t);
								w.getSset().addAll(c.getSset());
								match.getMatch().add(w);
						}
							}
							}
						}
				
				//matching t2 using t1 and the tip is nominal

			     if ((t_2.getRay().getTip().getIndividual()!=null)&&!(t_2.getRay().getTip().getIndividual().isEmpty())){
								
									Omega w=new Omega();
									w.setS(st_1);
									w.setT(t_2);
									for(Omega c: match.getMatch()) {
										if(c.getS().equals(st_2)&&c.getT().equals(t_1)){	
									for(Startype w1: c.getSset()) {
										Startype w2=new Startype();
										w2.setAddress(w1.getAddress());
										w2.setCore(t_2.getRay().getTip(), rd);
										w2.setTriples(w1.getTriples());
										if(!w2.getAddress().getSstar().contains(w2)) {
										w2.getAddress().getSstar().add(w2);
										for(Triple t2:w2.getTriples()) {
											for(Omega x: match.getMatch()) {
												if(x.getS().equals(st_2)){
													for(Triple p:st_2.getTriples()) {
														if(p.getRay().equals(t2.getRay())&&x.getT().equals(p)) {
															Omega v=new Omega();
															v.setS(w2);
															v.setT(t2);
															v.setSset(x.getSset());
														}
													}
												}}}
										}
										w.getSset().add(w2);

										match.getMatch().add(w);
										matched=true;

									}
										}
									}
								}
				

		else {
			if(!(l.hasNext(ct,l))) {
		

				System.out.println("I'm creating a new layer in the compressed tableau for you");
				l_next=new Layer();
				l_next.setNominal(false);
				ct.getSlayer().add(l_next);
				Startype o=new Startype();
				Set<OWLClassExpression> concepts = rd.getConceptsFromPrimitiveAxioms(t_2.getRay().getTip().getConcepts(), new HashSet<OWLClassExpression>());
				//System.out.println("new star-type by exists: "+concepts);
				/* for(OWLClassExpression c:concepts) {
		            	Set<OWLClassExpression> c_=new HashSet<OWLClassExpression>();
		            	c_.add(c);
		            	 Set<OWLClassExpression> concepts_ = rd.getConceptsFromPrimitiveAxioms( c_, new HashSet<OWLClassExpression>());
		            	 System.out.println("exists each concept "+concepts_);
		            	 
		            }*/
				ConceptLabel cl=new ConceptLabel(concepts);
				o.setCore(cl, rd);
				Triple t_=new Triple();
				t_.setCore(cl);
				o.addTriple(t_);
				o.setAddress(l.next(ct,l));
				l.next(ct, l).getSstar().add(o);

				Omega c1=new Omega();
				c1.setS(st_1);
				c1.setT(t_2);
				c1.getSset().add(o);
				match.getMatch().add(c1);
				//initialization of the mf
				Omega c_=new Omega();
				c_.setS(o);
				c_.setT(t_);
				match.getMatch().add(c_);
				o.setNominal(false);

				System.out.println("We have created a new star-type of core: "+ o.getCore().toString());

			}

			// add the star-type
			//do we need the CT
			//this is false
			else   {
				System.out.print("There already existed a next  layer");
				/*for(Startype st : l.next(ct, l).getSstar()) {

					if(st.getCore().equals(t_2.getRay().getTip())) {
						Omega c1= new Omega();
									c1.setS(st_1);
									c1.setT(t_2);
									c1.getSset().add(st);
									match.getMatch().add(c1);
									matched=true;
								}
							
						}
						
				
				if(matched==false) {*/

					for(Omega c_1: match.getMatch()) {

						if(c_1.getS().equals(st_2) &&c_1.getT().equals(t_1)) {

								Omega w=new Omega();
								w.setS(st_1);
								w.setT(t_2);
								for(Startype w1: c_1.getSset()) {

									Startype w2=new Startype();
									w2.setAddress(w1.getAddress());
									if(!w2.getAddress().getSstar().contains(w2)) {
										System.out.print("There already existed a next  layer");
									w2.getAddress().getSstar().add(w2);
									//w2.setCore(t_2.getRay().getTip(), rd);
									//here
									Set<OWLClassExpression> concepts = rd.getConceptsFromPrimitiveAxioms(t_2.getRay().getTip().getConcepts(), new HashSet<OWLClassExpression>());
									ConceptLabel cl=new ConceptLabel(concepts);
									w2.setCore(cl, rd);
									w2.setTriples(w1.getTriples());
									for(Triple t_:w2.getTriples()) {

										for(Omega x: match.getMatch()) {
											if(x.getS().equals(st_2)){

												for(Triple p:st_2.getTriples()) {

													if(p.getRay().equals(t_.getRay())&&x.getT().equals(p)) {
														Omega v=new Omega();
														v.setS(w2);
														v.setT(t_);
														v.setSset(x.getSset());
														match.getMatch().add(v);
													}

												}
											}}}
									}
									w.getSset().add(w1);
									match.getMatch().add(w);

									matched=true;

								}

							
						//}
					}
				}
			}
		}	


	}


	public  void matchingMerge(Startype s1, Startype s2, Startype s12, CompressedTableau ct, MatchingFn match, ReasoningData rd) {
		Set<Startype> s_1=new HashSet<Startype>();
		s_1.add(s1);
		Set<Startype> s_2=new HashSet<Startype>();
		s_2.add(s2);
		//match to the successor w.r.t s1
		for(Triple t12:s12.getTriples()) {
			for(Triple t1:s1.getTriples()) {
				if(t1.getRay().getRidge().equals(t12.getRay().getRidge())) {
					for(Omega o:match.getMatch()) {
						if(o.getS().equals(s1)&&o.getT().equals(t1)) {
							
							Omega o_=new Omega();
							o_.setS(s12);
							o_.setT(t12);
							o_.getSset().addAll(o.getSset());
							match.getMatch().add(o_);
						
						}
						}
						
					}
					
				}
			}
		//match to the successor w.r.t s2
		for(Triple t12:s12.getTriples()) {
			for(Triple t2:s2.getTriples()) {
				if(t2.getRay().getRidge().equals(t12.getRay().getRidge())) {
					for(Omega o:match.getMatch()) {
						if(o.getS().equals(s1)&&o.getT().equals(t2)) {
							Omega o_=new Omega();
							o_.setS(s12);
							o_.setT(t12);
							o_.getSset().addAll(o.getSset());
							match.getMatch().add(o_);	
						}
						
					}
					}
					
				}
			}
			
		for(Startype w:s1.getAddress().getSstar()) {
			for(Triple tw:w.getTriples()) {
				for(Omega o:match.getMatch()) {
					
				if(o.getS().equals(w)&&o.getT().equals(tw)&&(o.getSset().contains(s1)||o.getSset().equals(s_1))) {
				
					Startype wCopy=new Startype();
					wCopy.setAddress(w.getAddress());
					
			//	wCopy.setCore(w.getCore());
			//	wCopy.getCore().setConcepts(w.getCore().getConcepts());
					//wCopy.setCore(w.getCore(), rd);
					for(Triple tr:w.getTriples()) {
						if(!tr.getRay().equals(tw.getRay())) {
						
						wCopy.getTriples().add(tr);
					
						}
						else
						{
							
							tr.getRay().getTip().setConcepts(s12.getCore().getConcepts());
							tr.getRay().getTip().setIndividual(s12.getCore().getIndividual());
							wCopy.getTriples().add(tr);
							
							Omega o_=new Omega();
							o_.setS(wCopy);
							o_.setT(tr);
							o_.getSset().add(s12);
							match.getMatch().add(o_);
						}
					}
						
					s1.getAddress().getSstar().add(wCopy);
					ConceptLabel cl= new ConceptLabel(w.getCore().getConcepts(),w.getCore().getIndividual());
					wCopy.setCore(cl, rd);
				//	System.out.println(s1.getAddress().getSstar().size());
					
				}}}}

		for(Startype w:s1.getAddress().getSstar()) {
			for(Triple tw:w.getTriples()) {
				for(Omega o:match.getMatch()) {
	
				if(o.getS().equals(w)&&o.getT().equals(tw)&&(o.getSset().contains(s2)||o.getSset().equals(s_2))) {
					//	
					
						Startype wCopy=new Startype();
						wCopy.setAddress(w.getAddress());
				
						
						//wCopy.setCore(w.getCore(), rd);
						for(Triple tr:w.getTriples()) {
							if(!tr.getRay().equals(tw.getRay())) {
							
							wCopy.getTriples().add(tr);
						
							}
							else
							{
								tr.getRay().getTip().setConcepts(s12.getCore().getConcepts());
								
								tr.getRay().getTip().setIndividual(s12.getCore().getIndividual());
								wCopy.getTriples().add(tr);
								Omega o_=new Omega();
								o_.setS(wCopy);
								o_.setT(tr);
								o_.getSset().add(s12);
								match.getMatch().add(o_);
							}
						}
					
						s1.getAddress().getSstar().add(wCopy);
						ConceptLabel cl= new ConceptLabel(w.getCore().getConcepts(),w.getCore().getIndividual());
						wCopy.setCore(cl, rd);	
					
						//System.out.println(wCopy.getCore().getConcepts());
			
						
				//	
					//pre- of the pred
					
				
			/*	for(Startype z:s1.getAddress().getSstar()) {
				for(Triple t:z.getTriples()) {
					for(Omega o_:match.getMatch()) {
						if(o_.getS().equals(z)&&o_.getT().equals(t)&&o_.getSset().contains(w)) {
						
							o.getSset().add(wCopy);
					}
					
					
				}
			}
			}*/
			
		}
				}
			}
		}
	}

}
