package fr.anonymous.reasoner;

/*
 *
 */
import java.io.File;
import java.io.FileNotFoundException;
import java.util.HashSet;
import java.util.Scanner;
import java.util.Set;

import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.util.DefaultPrefixManager;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;

//This new class  converts link keys in EDOAL to OWL assertions. 
//Then, test your class carefully and upload to gitlab Some code in "Data.java".
//For testing, you can ask JD for files with link keys in EDOAL 
public class LoadingLinkeys {
	private static OWLDataFactory factory = new OWLDataFactoryImpl();

	public LoadingLinkeys() {
		// TODO Auto-generated constructor stub
	}


	// java.util.Scanner's default delimiter is whitespace.
	public Set<Linkey> EDOALtoLKs(File f) {
		PrefixManager manager = new DefaultPrefixManager("file:" + f.getAbsolutePath().substring(0, f.getAbsolutePath().lastIndexOf(f.getName())));
		Set<Linkey> linkeys = new HashSet<>();
		try {
			Scanner myReader = new Scanner(f);
			String s;
			while (myReader.hasNext()) {
				s = myReader.next();
				if (s.startsWith("rdf:about=\"#cell-with-linkkey\"")) {

					Linkey lk;
					ConceptPair PairOfConcepts = new ConceptPair();
					Set<PropertyPair> propertySet = new HashSet<>();
					OWLClassExpression class_1, class_2;
					myReader.next();
					s = myReader.next();

					if (s.startsWith("rdf:about")) {
						int st = s.indexOf("\"");
						int e = s.lastIndexOf("\"");
						s = s.substring(st + 1, e);
						class_1 = factory.getOWLClass("<"+s+">", manager);
					//	System.out.println(class_1);
						PairOfConcepts.setFirstConcept(class_1);
					}
					 myReader.next();
					 myReader.next();
					s = myReader.next();
					if (s.startsWith("rdf:about")) {
						int st = s.indexOf("\"");
						int e = s.lastIndexOf("\"");
						s = s.substring(st + 1, e);

						class_2 = factory.getOWLClass("<"+s+">", manager);

					//	System.out.println(class_2);
						PairOfConcepts.setSecondConcept(class_2);

					}



					 myReader.next();
					 myReader.next();
					 myReader.next();
					 myReader.next();
					myReader.next();

					 s=myReader.next();

					while (!s.endsWith(" </Intersects>") && !s.endsWith("</linkkey>") && myReader.hasNext()) {
						if (s.startsWith("<Intersects")) {

							PropertyPair pp = new PropertyPair();
							myReader.next();
							s = myReader.next();

							if (s.startsWith("rdf:about")) {

								int st = s.indexOf("\"");
								int e = s.lastIndexOf("\"");
								s = s.substring(st + 1, e);

								OWLPropertyExpression p1 = factory.getOWLObjectProperty("<"+s+">", manager);
							//	System.out.println(p1);
								pp.setFirstProperty(p1);
							}
							// myReader.next();
							//
							//
							myReader.next();
							s = myReader.next();

							if (s.startsWith("rdf:about")) {
								int st = s.indexOf("\"");
								int e = s.lastIndexOf("\"");
								s = s.substring(st + 1, e);

								OWLPropertyExpression p2 = factory.getOWLObjectProperty("<"+s+">", manager);
							//	System.out.println(p2);
								pp.setSecondProperty(p2);
							}

							propertySet.add(pp);
						}

						// myReader.next();
						s=myReader.next();
					}
					lk = new Linkey(PairOfConcepts, propertySet);
					linkeys.add(lk);
				}
			}


		} catch (FileNotFoundException e) {

			System.out.println(e);
		} catch (Exception e) {
			e.printStackTrace();
		}
		return linkeys;

	}


}