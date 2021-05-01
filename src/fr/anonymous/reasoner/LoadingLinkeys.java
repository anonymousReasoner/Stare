package fr.anonymous.reasoner;

/*
 *
 */
import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.InputStreamReader;
import java.util.HashSet;
import java.util.Scanner;
import java.util.Set;

import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLPropertyExpression;
import org.semanticweb.owlapi.model.PrefixManager;
import org.semanticweb.owlapi.util.DefaultPrefixManager;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;

//This new class  converts link keys in EDOAL to OWL assertions. 
//Then, test your class carefully and upload to gitlab Some code in "Data.java".
//For testing, you can ask JD for files with link keys in EDOAL 
public class LoadingLinkeys {
	private static OWLDataFactory factory=new OWLDataFactoryImpl();

	public LoadingLinkeys() {
		// TODO Auto-generated constructor stub
	}

	//public OWLClassExpression stringToClass(String s, OWLDataFactory factory) {

	//	 OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
	//  OWLDataFactory factory = manager.getOWLDataFactory();
	//     OWLClassExpression class_1string= factory.getOWLClass(IRI.create(s));
	//	return class_1string;
	//

	//}
	// java.util.Scanner's default delimiter is whitespace.
	public 	Set<Linkey> EDOALtoLKs(File f){
		PrefixManager manager=new DefaultPrefixManager("file:"+f.getAbsolutePath().substring(0,f.getAbsolutePath().lastIndexOf(f.getName())));
		Set<Linkey> linkeys = new HashSet<Linkey>();
		try
		{
			Scanner myReader = new Scanner(f);
			//	System.out.println("after scanner");
			FileInputStream fis=new FileInputStream(f);
			BufferedReader br = new BufferedReader(new InputStreamReader(fis));
			String s=null;
			while( myReader.hasNext() != false)
			{
			
						s=	myReader.next();
						
						
						if(s.startsWith("rdf:about=\"#cell-with-linkkey\"")) {
							
							s=	myReader.next();
							
							Linkey lk=null;
							ConceptPair PairOfConcepts=new ConceptPair();
							Set<PropertyPair> propertySet=new HashSet<PropertyPair>();
							OWLClassExpression class_1,class_2;
							//System.out.println(s);
							s=myReader.next();
							
							if(s.startsWith("rdf:about"))
							{
								int st=s.indexOf("\"");
								int e=s.lastIndexOf("\"");
								s=s.substring(st+1,e);
								//System.out.println("First Class"+ s);
								class_1=factory.getOWLClass(s,manager);
								PairOfConcepts.setFirstConcept(class_1);
							}
						
						//
							s=myReader.next();
							s=myReader.next();

						//if(s.startsWith("<align:entity2")) {
							s=myReader.next();
							if(s.startsWith("rdf:about"))
							{
								int st=s.indexOf("\"");
								int e=s.lastIndexOf("\"");
								s=s.substring(st+1,e);
							//	System.out.println("Second Class" +s);
								class_2=factory.getOWLClass(s, manager);



								PairOfConcepts.setSecondConcept(class_2);

							}

						//}
						
						s=	myReader.next();
						s=	myReader.next();
						s=  myReader.next();
						s=  myReader.next();
						s=	myReader.next();
						s=	myReader.next();
						
						//
						while(!s.endsWith(" </Intersects>")&&!s.endsWith("</linkkey>")&&myReader.hasNext() != false) {
							s=	myReader.next();
							
						if(s.startsWith("<Intersects")) {
							PropertyPair pp=new PropertyPair();
							s=myReader.next();
							
							
							s=myReader.next();
							
							if(s.startsWith("rdf:about"))
							{
								int st=s.indexOf("\"");
								int e=s.lastIndexOf("\"");
								
								s=s.substring(st+1,e);
								//System.out.println(s);
								OWLPropertyExpression p1 = factory.getOWLObjectProperty(s,manager);
								
								pp.setFirstProperty(p1);

							
							}
							s=myReader.next();
							s=myReader.next();
							s=myReader.next();
						
							if(s.startsWith("rdf:about"))
							{
								
								
									int st=s.indexOf("\"");
									int e=s.lastIndexOf("\"");
									

								s=s.substring(st+1,e);
								//System.out.println(s);
								
								OWLPropertyExpression p2 = factory.getOWLObjectProperty(s,manager);
								
								pp.setSecondProperty(p2);


							//}
							}
							
							propertySet.add(pp);
						}
						
						s=	myReader.next();
					
						}
						//System.out.println("lk added");
						
					
						
					 lk= new Linkey(PairOfConcepts,propertySet) ;
					
					//lk=EDOALtoLK(f);
					linkeys.add(lk);
					}
						//s=	myReader.next();
						//System.out.println(s);
						
						}
				

			
		}

		catch (FileNotFoundException e){

			System.out.println(e);
		}
		catch(Exception e)
		{
			e.printStackTrace();
		}
	//System.out.println(linkeys.size());
		return linkeys;

	}


	/*public Linkey EDOALtoLK(File f){
		
	
		PrefixManager manager=new DefaultPrefixManager("file:"+f.getAbsolutePath().substring(0,f.getAbsolutePath().lastIndexOf(f.getName())));

		ConceptPair PairOfConcepts=new ConceptPair();
		Set<PropertyPair> propertySet=new HashSet<PropertyPair>();
		OWLClassExpression class_1,class_2;
		try
		{   Scanner myReader = new Scanner(f);
			FileInputStream fis=new FileInputStream(f);
			BufferedReader br = new BufferedReader(new InputStreamReader(fis));
			String s=null;
			while( myReader.hasNext() != false)
			{
				s=	myReader.next();
				if(s.startsWith("<align:entity1")) {
					s=myReader.next();
					if(s.startsWith("rdf:about"))
					{
						s=s.substring(11,12);
						//System.out.println("First Class"+ s);
						class_1=factory.getOWLClass(s,manager);
						PairOfConcepts.setFirstConcept(class_1);
					}
				}

				if(s.startsWith("<align:entity2")) {
					s=myReader.next();
					if(s.startsWith("rdf:about"))
					{
						s=s.substring(11,12);
						//System.out.println("Second Class" +s);
						//	 class_2=factory.getOWLClass(IRI.create(s));
						class_2=factory.getOWLClass(s, manager);



						PairOfConcepts.setSecondConcept(class_2);

					}

				}

				if(s.startsWith("<Intersects")) {
					s=myReader.next();
					PropertyPair pp=new PropertyPair();
					if(s.startsWith("<property1") ){
						s=myReader.next();
						s=s.substring(11,12);

						OWLPropertyExpression p1 = factory.getOWLObjectProperty(s,manager);
					//	System.out.println(p1);
						pp.setFirstProperty(p1);

						s=myReader.next();
						s=myReader.next();
						s=myReader.next();

						s=s.substring(11,12);
						// System.out.println(s);
						OWLPropertyExpression p2 = factory.getOWLObjectProperty(s,manager);
						
						pp.setSecondProperty(p2);


					}

					propertySet.add(pp);
				}
				if(s.startsWith("</Linkkey>")) {
					break;
				}
				
System.out.println("-----------------------------------------");
			}
			myReader.close();
			br.close();

		} //END Try

		catch(Exception e)
		{
			e.printStackTrace();

		}

		return new  Linkey(PairOfConcepts,propertySet);
		

	}*/
	

	}
