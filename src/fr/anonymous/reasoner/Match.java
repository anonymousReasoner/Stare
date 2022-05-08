package fr.anonymous.reasoner;
import java.util.List;
import java.util.concurrent.CopyOnWriteArrayList;
import org.semanticweb.owlapi.model.*;

public class Match {
	CopyOnWriteArrayList<Succ> match;
	public int id;

	public Match() {
		this.match = new CopyOnWriteArrayList<>();
	}

	public CopyOnWriteArrayList<Succ> getMatch() {
		return match;
	}

	public void setMatch() {
		this.match = new CopyOnWriteArrayList<>();
	}

	//	st_1 is the derived star-type, st_2 is the original
	public void matchingCore(Startype s_1, Startype s_2, ReasoningData data, CompressedTableau ct) {

		// I have to search for every predecessor of s_1
		for (Startype pred : s_1.getAddress().previous(ct).getSstar()) {

			for (Succ s : pred.getSucc().getMatch()) {

				// create a copy of it, such that the matching
				//triple is modified
				if (s.getSset().contains(s_1)||s.getSset().equals(s_1)) {
					Startype copy_pred = new Startype();
					copy_pred.setCore(pred.getCore());
					List<Triple> triples = pred.getTriples();
					Triple copy_t = s.getT();
					triples.remove(copy_t);
					copy_t.getRay().setTip(s_2.getCore());
					triples.add(copy_t);
					copy_pred.setTriples(triples);
					//the new successor (s_2) through the modified triple
					Succ sc = new Succ();
					sc.setT(copy_t);
					sc.getSset().add(s_2);
					copy_pred.getSucc().getMatch().add(sc);
					System.out.println("Creating a new predecessor of core: "+ copy_pred.getCore().getIndividual());
					// predecessors of the predecessor
					for (Startype Ppred : pred.getAddress().previous(ct).getSstar()) {
						for (Succ Ps : Ppred.getSucc().getMatch()) {
							if (Ps.getSset().contains(pred)) {
								Ps.getSset().add(copy_pred);
							}
						}
					}
					// successors of the predecessor
					for (Succ Ps : pred.getSucc().getMatch()) {
						if (!Ps.getT().equals(copy_t)) {
							Succ sca = new Succ();
							sca.setT(Ps.getT());
							sca.setSset(Ps.getSset());
							copy_pred.getSucc().getMatch().add(sca);
						}

					}
					//successors of s_2
					for (Succ ss : s_1.getSucc().getMatch()) {
						Succ succ = new Succ();
						succ.setT(ss.getT());
						ss.setSset(ss.getSset());
						s_2.getSucc().getMatch().add(ss);
					}

				}
			}

		}

	}


	//s_1 and t_1 are resp the old star-type and triple, s_2 and t_2 are resp the derived star-type and triple
	public void matchTriple(Startype s_1, Triple t_1, Startype s_2, Triple t_2, CompressedTableau ct, ReasoningData rd, OWLOntology ontology, OWLDataFactory data) {

		//the predecessors of s_1 are the same as the predecessors of s_2
		for (Startype s : s_1.getAddress().previous(ct).getSstar()) {
			for (Succ ss : s.getSucc().getMatch()) {
				if (ss.getSset().contains(s_1)) {
					ss.getSset().add(s_2);
				}
			}
		}
		// the successors of s_2 through triples other than t_2 are not changed
		//System.out.println("Before matching to the successors");
		for (Succ s : s_1.getSucc().getMatch()) {

			//if t_1 is not null
			if (!s.getT().equals(t_1)) {
				Succ ss = new Succ();
				ss.setT(s.getT());
				ss.setSset(s.getSset());
				s_2.getSucc().getMatch().add(ss);
			}
				// I have to change the successor
			if (t_1 != null) {
					for (Startype st : s.getSset()) {
						Startype star = new Startype();
						star.setTriples(st.getTriples());
						star.setCore(t_2.getRay().getTip());
						Succ ss = new Succ();
						ss.setT(t_2);
						ss.getSset().add(star);
						s_2.getSucc().getMatch().add(ss);
						// the successor of the successor
					}
				}
			}
		OWLClassExpression superClass = null;
		OWLClassExpression subClass = null;
		boolean to=false;
				// exists rule
				// if t_1 is not null in this case we have to create a new star-type in the next layer, if the next layer exist,
				// otherwise we have to create a new layer

				if(t_1==null) {
					Startype new_star = new Startype();
					if (!s_1.getAddress().hasNext(ct, s_1.getAddress())) {
						Layer layer = new Layer();
						layer.setId(s_1.getAddress().getId()+1);
						ct.getSlayer().add(layer);
						layer.getSstar().add(new_star);
						new_star.setAddress(layer);
						System.out.println("I have added a new layer of number "+ layer.getId());
					}
					else{
						new_star.setAddress(s_1.getAddress().next(ct, s_1.getAddress()));
						s_2.getAddress().next(ct, s_1.getAddress()).getSstar().add(new_star);

					}

					new_star.getCore().setConcepts(t_2.getRay().getTip().getConcepts());
				//	new_star.getCore().getConcepts().addAll(rd.getConceptsFromPrimitiveAxioms(t_2.getRay().getTip().getConcepts(), new HashSet<>()));
				//	new_star.sub(new_star, rd, ontology, ct);
					Succ sc = new Succ();
					sc.setT(t_2);
					sc.getSset().add(new_star);
					s_2.getSucc().getMatch().add(sc);

					//.getSstar().add(new_star);
				}

		}

	public void matchMerge(Startype s_1, Startype s_2, Startype s_12, ReasoningData rd, CompressedTableau ct) {
		// The core and the triples are changed
		// The triples are not changed but rather increased
		// First we start by the predecessors of the modified core
		// The predecessors of s1 and s2 become the predecessors of s12, for that I have to change the triple of the predecessor
		for (Startype pred : (s_1.getAddress().previous(ct).getSstar() )) {

			for (Succ s : pred.getSucc().getMatch()) {
				// create a copy of it, such that the matching
				//triple is modified
				if (s.getSset().contains(s_1)) {
					Startype copy_pred = new Startype();
					copy_pred.setCore(pred.getCore());
					List<Triple> triples = pred.getTriples();
					Triple copy_t = s.getT();
					triples.remove(copy_t);
					copy_t.getRay().setTip(s_12.getCore());
					triples.add(copy_t);
					copy_pred.setTriples(triples);
					//the new successor (s_2) through the modified triple
					Succ sc = new Succ();
					sc.setT(copy_t);
					sc.getSset().add(s_12);
					copy_pred.getSucc().getMatch().add(sc);

					// predecessors of the predecessor
					for (Startype Ppred : pred.getAddress().previous(ct).getSstar()) {
						for (Succ Ps : Ppred.getSucc().getMatch()) {
							if (Ps.getSset().contains(pred)) {
								Ps.getSset().add(copy_pred);
							}
						}
					}
					// The successors of the predecessor
					for (Succ Ps : pred.getSucc().getMatch()) {
						if (!Ps.getT().equals(copy_t)) {
							Succ sca = new Succ();
							sca.setT(Ps.getT());
							sca.setSset(Ps.getSset());
							copy_pred.getSucc().getMatch().add(sca);
						}
					}
					//successors of s_12 (the merge w.r.t the triples coming from s_1)
					for (Succ ss : s_1.getSucc().getMatch()) {
						Succ succ = new Succ();
						succ.setT(ss.getT());
						ss.setSset(ss.getSset());
						s_12.getSucc().getMatch().add(ss);
					}
				}
			}
			// The successors of s_12 w.r.t s_1
			for (Succ ss : s_1.getSucc().getMatch()) {
				Succ succ = new Succ();
				succ.setT(ss.getT());
				ss.setSset(ss.getSset());
				s_12.getSucc().getMatch().add(ss);
			}
		}
		// First star-type
		for (Startype pred : (s_2.getAddress().previous(ct).getSstar() )) {

			for (Succ s : pred.getSucc().getMatch()) {
				// create a copy of it, such that the matching
				//triple is modified
				if (s.getSset().contains(s_2)) {
					Startype copy_pred = new Startype();
					copy_pred.setCore(pred.getCore());
					List<Triple> triples = pred.getTriples();
					Triple copy_t = s.getT();
					triples.remove(copy_t);
					copy_t.getRay().setTip(s_12.getCore());
					triples.add(copy_t);
					copy_pred.setTriples(triples);
					//the new successor (s_2) through the modified triple
					Succ sc = new Succ();
					sc.setT(copy_t);
					sc.getSset().add(s_12);
					copy_pred.getSucc().getMatch().add(sc);

					// predecessors of the predecessor
					for (Startype Ppred : pred.getAddress().previous(ct).getSstar()) {
						for (Succ Ps : Ppred.getSucc().getMatch()) {
							if (Ps.getSset().contains(pred)) {
								Ps.getSset().add(copy_pred);
							}
						}
					}
					// The successors of the predecessor
					for (Succ Ps : pred.getSucc().getMatch()) {
						if (!Ps.getT().equals(copy_t)) {
							Succ sca = new Succ();
							sca.setT(Ps.getT());
							sca.setSset(Ps.getSset());
							copy_pred.getSucc().getMatch().add(sca);
						}
					}
					//successors of s_12 (i.e., the merge w.r.t the triples coming from s_2)
					for (Succ ss : s_2.getSucc().getMatch()) {
						Succ succ = new Succ();
						succ.setT(ss.getT());
						ss.setSset(ss.getSset());
						s_12.getSucc().getMatch().add(ss);
					}
					// The successors of s_12 w.r.t s_2
					for (Succ ss : s_2.getSucc().getMatch()) {
						Succ succ = new Succ();
						succ.setT(ss.getT());
						ss.setSset(ss.getSset());
						s_12.getSucc().getMatch().add(ss);
					}
				}
			}
		}
	}
}


