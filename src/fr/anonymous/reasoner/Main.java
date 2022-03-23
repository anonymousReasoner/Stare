package fr.anonymous.reasoner;
import java.io.File;
import java.time.Duration;
import java.time.Instant;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Scanner;
import java.util.Set;
import java.util.concurrent.CopyOnWriteArraySet;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.util.DefaultPrefixManager;
import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;

public class Main {
	public static void printMatchingPred( CompressedTableau ct) {
		
		int i=1;
		for(Layer l:ct.getSlayer())
		{
			System.out.println("Layer: "+i);
			
			for(Startype st:l.getSstar()) {
				boolean pred=false;
				Set<Startype> s=new HashSet<>();
				s.add(st);
				System.out.print("I'm star-type of id: "+  st.getIdS()+ " and "+st.getCore().toString()+",");
			
				for(Succ o:st.getSucc().getMatch()) {
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
					for(Succ o:st.getSucc().getMatch()) {
						if(o.getSset().contains(st)||o.getSset().equals(s)) {
						
					
					System.out.println(st.getCore().toString()+" through the triple of id " +o.getT().getIdT()+" and "+ o.getT().getRay().getTip().toString());
				}
					}
				
			}
			}
			i++;
		}
	
		
		
	} 
	public static void printMatchingSucc( CompressedTableau ct) {
		int i=1;
		
		for(Layer l:ct.getSlayer())
		{
			System.out.println("Layer: "+i);
			
			for(Startype st:l.getSstar()) {
				System.out.println("I'm star-type of id: "+  st.getIdS()+ " and "+ st.getCore().toString()+",");
				for(Triple t:st.getTriples()) {
					for(Succ o:st.getSucc().getMatch()) {
						if(o.getT().equals(t)) {
							System.out.println(" I'm matched through the triple of id " +o.getT().getIdT()+" and "+ o.getT().getRay().getTip().toString()+ " to: "+ "with the property"+o.getT().getRay().getRidge().getRoles());
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
		int idS = 1;
		int nextIdS = 2;
		String directoryName;  // Directory name entered by the user.
		File file;        // File object referring to the directory.
		Scanner scanner;       // For reading a line of input from the user.
		File f_exlk = null;
		scanner = new Scanner(System.in);  // scanner reads from standard input.
		System.out.print("Enter a directory name of your ontology: ");
		directoryName = scanner.nextLine().trim();
		file = new File("test/" + directoryName);
		System.out.print("Enter a directory name of your alignment: ");
		String alignment = scanner.nextLine().trim();
		System.out.print("Enter your strategy: all for the OneShot strategy,\n iter for the OneByOne strategy,\n com for the Combined strategy ");
		String strategy = scanner.nextLine().trim();
		OWLDataFactory data=new OWLDataFactoryImpl();

			if (!alignment.isEmpty())
				f_exlk = new File("test/" + alignment);
			OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
			OWLOntology ontology = null;
			Instant start = Instant.now();
			// long startTime = System.currentTimeMillis();
			try {
				ontology = manager.loadOntologyFromOntologyDocument(file);
				Set<OWLClassAxiom> classes = ontology.getGeneralClassAxioms();
				for(OWLAxiom c:classes) {
					System.out.println(c);
				}
			} catch (OWLOntologyCreationException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}

			//MatchingFn mf=new MatchingFn();
			CompressedTableau ct = new CompressedTableau();
			ReasoningData rd;
			CopyOnWriteArraySet<Layer> slayer = new CopyOnWriteArraySet<>();
			ct.setSlayer(slayer);
			boolean lk = false;
			if (f_exlk != null) {

					lk = true;
					LoadOntology load = new LoadOntology(ontology, 1, f_exlk);
					rd = load.getData();
					PrefixManager pmanager = new DefaultPrefixManager("file:" + file.getAbsolutePath().substring(0, file.getAbsolutePath().lastIndexOf(file.getName())));
					// here is the initialization function
					ct.init(ontology,rd, pmanager, ct);
					//calling the rules
					ct.main(ct, ontology, rd, lk,strategy,data);

			}
			else {
				LoadOntology load = new LoadOntology(ontology, 1);
				rd = load.getData();
				PrefixManager pmanager = new DefaultPrefixManager("file:" + file.getAbsolutePath().substring(0, file.getAbsolutePath().lastIndexOf(file.getName())));
				// here is the initialization function
				ct.init(ontology,rd, pmanager, ct);
				//calling the rules
				ct.main(ct, ontology, rd, lk, strategy, data);
			}
			Instant end = Instant.now();
			System.out.println("The execution time is " + Duration.between(start, end).toMillis() + "ms");
			System.out.println("\nQuestion:Is the ontology consistent? \n" + "Answer: " + "" + ct.checkNew(ct, rd, lk, ct.getSlayer().stream().iterator().next()));
			Iterator<Layer> layers_iterator = ct.getSlayer().iterator();
			System.out.println("The number of layers in the compressed tableau are:" + ct.getSlayer().size());
			int i = 0;
			while (layers_iterator.hasNext()) {
				Layer l = layers_iterator.next();
				i++;
				System.out.println("Is Layer " + i + " nominal?\n" + l.isNominal() + ", and it contains " + l.getSstar().size() + " star-types .");
				Iterator<Startype> layers_stars = l.getSstar().iterator();

				while (layers_stars.hasNext()) {
					Startype st = layers_stars.next();
					System.out.println("Star-type of id: " +st.getIdS() + " and Individuals: " + st.getCore().getIndividual());
					//+ " of concepts" + st.getCore().getConcepts());
					System.out.println(" Am I saturated? " + st.isSaturated(st.getAddress(), rd, ct) + " Am I blocked? " + st.getAddress().isBlocked(st, ct));
					System.out.println("My nbr of triples: " + st.getTriples().size());

				//	st.setIdS(idS);
					idS = nextIdS;
					nextIdS++;
					Iterator<Triple> star_triples = st.getTriples().iterator();
					int idT = 1;
					int nextIdT = 2;
					while (star_triples.hasNext()) {
						Triple t = star_triples.next();
						t.setIdT(idT);
						idT = nextIdT;
						nextIdT++;
					}
				}
			}
			System.out.println("The number of layers in the compressed tableau are:" + ct.getSlayer().size());
			System.out.print("Do you want to display the matching function: (y/n) ");
			String decision = scanner.nextLine().trim();
			if (decision.equalsIgnoreCase("y")) {
				printMatchingPred(ct);
				System.out.println("---------------------------------------------------------");
				printMatchingSucc(ct);
			}
			Runtime runtime = Runtime.getRuntime();
			// Calculate the used memory
			long memory = runtime.totalMemory() - runtime.freeMemory();
			System.out.println("Used memory is mb: " + memory / 1000000);
		}// TODO Auto-generated method stub
}
