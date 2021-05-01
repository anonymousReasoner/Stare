package fr.anonymous.reasoner;
import java.io.File;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Scanner;
import java.util.Set;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.CopyOnWriteArraySet;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.PrefixManager;
import org.semanticweb.owlapi.util.DefaultPrefixManager;

public class Main {
	public static void printMatchingPred(MatchingFn mf, CompressedTableau ct) {
		
		int i=1;
		for(Layer l:ct.getSlayer())
		{
			System.out.println("Layer: "+i);
			
			for(Startype st:l.getSstar()) {
				boolean pred=false;
				Set<Startype> s=new HashSet<>();
				s.add(st);
				System.out.print("I'm star-type of id: "+  st.getIdS()+ " and "+st.getCore().toString()+",");
			
				for(Omega o:mf.getMatch()) {
				if(o.getSset().contains(st)||o.getSset().equals(s)) {
					pred=true;
					
				}
				}
			
				if(pred==false) {
					System.out.println(" and I don't have a predecessor");
				}
			
				else
				{
					System.out.println("my predecessors are: ");
					for(Omega o:mf.getMatch()) {
						if(o.getSset().contains(st)||o.getSset().equals(s)) {
						
					
					System.out.println(o.getS().getCore().toString()+" through the triple of id " +o.getT().getIdT()+" and "+ o.getT().getRay().getTip().toString());
				}
					}
				
			}
			}
			i++;
		}
	
		
		
	} 
	public static void printMatchingSucc(MatchingFn mf, CompressedTableau ct) {
		int i=1;
		
		for(Layer l:ct.getSlayer())
		{
			System.out.println("Layer: "+i);
			
			for(Startype st:l.getSstar()) {
				boolean succ=false;
				System.out.println("I'm star-type of id: "+  st.getIdS()+ " and "+ st.getCore().toString()+",");
				for(Triple t:st.getTriples()) {
					for(Omega o:mf.getMatch()) {
						if(o.getS().equals(st)&&o.getT().equals(t)) {
							succ=true;
							System.out.println(" I'm matched through the triple of id " +o.getT().getIdT()+" and "+ o.getT().getRay().getTip().toString()+ " to: ");
							for(Startype w:o.getSset()) {
								
								System.out.println(" star-type of: "+ w.getCore().toString()+",");
							}
							
						}
					}
					
				}
			}
			i++;
			}
		
	}

	public static void main(String[] args) {
int idS=1;
int nextIdS=2;
		 String directoryName;  // Directory name entered by the user.
	        File file;        // File object referring to the directory.
	        String[] files;        // Array of file names in the directory.
	        Scanner scanner;       // For reading a line of input from the user.

	        scanner = new Scanner(System.in);  // scanner reads from standard input.

	        System.out.print("Enter a directory name of your ontology: ");
	        directoryName = scanner.nextLine().trim();
	        file = new File("test/"+directoryName);
	        System.out.print("Enter a directory name of your alignment: ");
	        String alignment = scanner.nextLine().trim();
	        File f_exlk=new File("test/"+alignment);
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
	

		OWLOntology ontology=null;

		try {
			 ontology=manager.loadOntologyFromOntologyDocument(file);
			 //ontology=manager.loadOntologyFromOntologyDocument(f_ex2);
		} catch (OWLOntologyCreationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		LoadOntology load=new LoadOntology(ontology,1,f_exlk );
		ReasoningData rd= load.getData();
		PrefixManager pmanager=new DefaultPrefixManager("file:"+file.getAbsolutePath().substring(0,file.getAbsolutePath().lastIndexOf(file.getName())));
	//System.out.println("file:"+file.getAbsolutePath().substring(0,file.getAbsolutePath().lastIndexOf(file.getName())));
		MatchingFn mf=new MatchingFn();
		CompressedTableau ct=new CompressedTableau();
		CopyOnWriteArraySet<Layer> slayer= new CopyOnWriteArraySet<Layer>();
		ct.setSlayer(slayer);
		
		// here is the initialization function 
		ct.init(ontology, rd,pmanager,ct, mf);
		//calling the rules
		
	    
	    ct.main(ct,mf, ontology, rd);
    //
	    Iterator<Layer> layers_iterator=ct.getSlayer().iterator();
	
		 System.out.println("The number of layers in the compressed tableau are:" +ct.getSlayer().size());
		 int i=0;
		 Layer l_0 = null;
		
		 while(layers_iterator.hasNext())
		 {
			 Layer l=layers_iterator.next();
			
			 i++;
			System.out.println("Is Layer "+i+ " nominal?\n" + l.isNominal()+ ", and it contains "  + l.getSstar().size()+ " star-types ." );
			 Iterator<Startype> layers_stars=l.getSstar().iterator();
			
			while(layers_stars.hasNext()) {
				Startype st=layers_stars.next();
			
				st.setIdS(idS);
				idS = nextIdS;
				nextIdS++;
					//System.out.println(st.getIdS()+" "+st.getCore().toString());

				//	System.out.println("nbr of triples: "+st.getTriples().size());
				 Iterator<Triple> star_triples=st.getTriples().iterator();
				 int idT=1;
				 int nextIdT=2;
				 while(star_triples.hasNext()) {
					 Triple t=star_triples.next();
					 t.setIdT(idT);
					 idT = nextIdT;
						nextIdT++;
				 }
			
				
			}
		 }
		  System.out.print("Do you want to display the matching function: (y/n) ");
	        String decision = scanner.nextLine().trim();
	        if(decision.equalsIgnoreCase("y")) {
printMatchingPred(mf, ct);
System.out.println("---------------------------------------------------------");
printMatchingSucc(mf, ct);
	        }	
	//	System.out.println("\nThe following are the equality assertion in the ABox: "+rd.getABox().getSameIndAssers());
		
		System.out.println("\nQuestion:Is the ontology consistent? \n"+ "Answer: "+ ""+ct.checkNew(ct, mf, rd) );
		System.out.println("The time is " +System.currentTimeMillis()+ "ms");
		Runtime runtime = Runtime.getRuntime();
        // Run the garbage collector
        runtime.gc();
        // Calculate the used memory
        long memory = runtime.totalMemory() - runtime.freeMemory();
        System.out.println("Used memory is bytes: " + memory);
	}// TODO Auto-generated method stub

	

}
