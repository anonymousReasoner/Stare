package fr.anonymous.reasoner;

import org.openrdf.model.vocabulary.OWL;
import org.semanticweb.owlapi.model.OWLClassExpression;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.concurrent.CopyOnWriteArraySet;

public class Layer  {
	private boolean isNominal;
	private CopyOnWriteArraySet<Startype> Sstar;
	private int id;

	public Layer() {
		this.isNominal=false;
		this.Sstar= new CopyOnWriteArraySet<>();

	}

    public Layer(boolean nominal) {
		this.isNominal=nominal;
    }

    public boolean isNominal() {
		return isNominal;
	}
	public void setNominal(boolean isNominal) {
		this.isNominal = isNominal;
	}
	public Set<Startype> getSstar() {
		return Sstar;
	}
	public void setSstar(CopyOnWriteArraySet<Startype> sstar) {
		Sstar = sstar;
	}
	public boolean hasNext(	CompressedTableau ct, Layer layer) {

		boolean hasNext=false;

		Iterator<Layer> Iterate_layer=ct.getSlayer().iterator();

		while (Iterate_layer.hasNext() ) {
			if(Iterate_layer.next().equals(layer) )
				hasNext= Iterate_layer.hasNext();

		}
		return hasNext;
	}
	public Layer next(	CompressedTableau ct, Layer layer) {
		Layer l_next=null;
		Iterator<Layer> Iterate_layer=ct.getSlayer().iterator();
		while (Iterate_layer.hasNext() ) {
			if(Iterate_layer.next()==layer)


				l_next= Iterate_layer.next();



		}
		return l_next;

	}
	public boolean isBlocked(Startype st2,CompressedTableau ct) {

			for(Layer layer:ct.getSlayer()) {
				if(!layer.isNominal()&&!st2.getAddress().isNominal() ) {
					for(Startype st1:layer.getSstar()) {
						if(st1.getAddress().getId()<st2.getAddress().getId()&&st1.getIdS()<st2.getIdS()&&((st1.getCore().getConcepts().containsAll(st2.getCore().getConcepts())||st1.getCore().getConcepts().contains(st2.getCore().getConcepts())))) {
							System.out.println("I have id " + st2.getIdS() +" and layer" +st2.getAddress().getId() +" I'm blocked by star-type of id: "+ st1.getIdS() +" and layer " +st1.getAddress().getId() );
							System.out.println("My concepts are "+ st2.getCore().getConcepts()+" the concepts of my blocker are" + st1.getCore().getConcepts());
						//st2.setBlocked(true);
						return true;

						}
					}
				}
		}

		return false;
	}
	public Layer previous(	CompressedTableau ct) {
		Layer previous = null;
		for (Iterator<Layer> i = ct.getSlayer().iterator(); i.hasNext();) {
			Layer element = i.next();


			previous = element;
		}
		return previous;
	}
	public boolean satisfyLkandEqualities(ReasoningData rd) {
		//boolean lkSatisfy=true;
		Set<Linkey> lks=null;
		if(rd.getLKBox()!=null) {
			 lks = rd.getLKBox().getLks();
		}
		LinkkeyRules lkr=new 	LinkkeyRules();
		Set<Startype> stars=this.getSstar();
		if(lks!=null) {
			for (Startype star1 : stars) {
				for (Startype star2 : stars) {
					for (Linkey lk : lks) {
						// pb inside strong satisfaction
						if ( lkr.strongSatisfaction(star1, star2, lk)&&!lkr.isMergeContained(star1, star2) ) {
							//
						//	&& !lkr.isMergeContained(star1, star2)
System.out.println("Inside satisfy equalities and lks");
							return false;
						}

					}
				}

			}

		}
			return true;

	}

	public void setId(int i) {
		id = i;
	}

	public int getId() {
		return id;
	}
}

