

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.CopyOnWriteArrayList;

import org.semanticweb.owlapi.model.OWLIndividual;

import com.google.common.collect.SetMultimap;

public class Layer {
 private boolean isNominal;
 private CopyOnWriteArrayList<Startype> Sstar;
 public Layer() {
	 this.isNominal=false;
	 //this.Sstar= Collections.synchronizedList(new ArrayList<Startype>());
	 this.Sstar= new CopyOnWriteArrayList<Startype>();
	 
 }
public boolean isNominal() {
	return isNominal;
}
public void setNominal(boolean isNominal) {
	this.isNominal = isNominal;
}
public List<Startype> getSstar() {
	return Sstar;
}
public void setSstar(CopyOnWriteArrayList<Startype> sstar) {
	Sstar = sstar;
}
public boolean hasNext(	CompressedTableau ct, Layer layer) {

boolean hasNext=false;

Iterator<Layer> Iterate_layer=ct.getSlayer().iterator();

	while (Iterate_layer.hasNext() ) {
		if(Iterate_layer.next().equals(layer) )
		
				
			//System.out.println(Iterate_layer.hasNext());
					hasNext= Iterate_layer.hasNext();
				
	}
	//System.out.print("Has next");
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
public boolean isBlocked(Startype st2,CompressedTableau ct, Layer l) {
	boolean blocked=false;
	if(!st2.isNominal()) {
	for(Layer layer:ct.getSlayer()) {
		if(!layer.isNominal()) {
			
		for(Startype st1:layer.getSstar()) {
			
			int j=ct.getSlayer().indexOf(st2.getAddress());
			
			int i=ct.getSlayer().indexOf(st1.getAddress());
			
			if((st2.getAddress()!=st1.getAddress())&&!st2.getAddress().isNominal()&&!st1.getAddress().isNominal() &&i<j ) {
				
		if(st1.getCore().getConcepts().equals(st2.getCore().getConcepts())||st1.getCore().getConcepts().contains(st2.getCore().getConcepts())) {
			
			
			blocked=true;
			
		}
		}
		}
		
		}
	}
	}
	
	return blocked;
}
public Layer previous(	CompressedTableau ct, Layer layer) {
	Layer previous = null;
	for (Iterator<Layer> i = ct.getSlayer().iterator(); i.hasNext();) {
		Layer element = i.next();

	    // Do something with "element" and "previous" (if not null)

	    previous = element;
	}
	return previous;
}
public boolean satisfyLkandEqualities(ReasoningData rd) {
	boolean satisfy=true;
	Set<Linkey> lks=rd.getLKBox().getLks();
		LinkkeyRules lkr=new 	LinkkeyRules();
	List<Startype> stars=this.getSstar();
	
		for(Startype star1:stars)
		{
			for(Startype star2:stars) {
			for(Linkey lk:lks)
			if(lkr.strongSatisfaction(star1, star2, lk)) {
			if(!this.getSstar().contains(lkr.merge(star1,star2, rd))) {
				satisfy=false;
			}
			}
		}
		}
		
	return satisfy;
	
}
}
