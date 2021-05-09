# stare
****Description****

The project aims to develop a reasoner which is based on a new
optimization technique, called compressed-tableau. This reasoner allows
to reason on ontologies expressed in Description Logics (e.g. OWL
ontologies) containing link keys. A link key is a set of pairs of properties that identify equal entities of two classes.
For example **{(prenom ,firstname)**, **(nom, lastname)}** for **(Auteur, Author)** which states that if an instance **a** of the class **Auteur** and an instance **b** of the class **Author** share, resp., a value for the properties **prenom** and **firstname**, a value for **nom** and **lastname**, and a value for **ne** and **birthdate**, then they are the same entity. 

****Installation****
# Clone the repository.
# Compile

```javac -cp "lib/*" src/fr/anonymous/reasoner/*.java -d bin```

# Run
From the root folder type:

```java -cp bin:"$(printf %s: lib/*.jar)" fr.anonymous.reasoner.Main```



**Running the test data sets**
You can choose among 2 couples of ontologies and alignments:
 (chainedLink.owl,LKSchainedLink.rdf), (consistency.owl, consistencyLK.rdf)
- Choose your ontology then press enter.
- Enter the name of alignment then press enter.
- If you want to display the matching function enter "y" then press enter.


****Work in progress****
- Testing with bigger data sets.


****Future work****
- Generating latex figures from the code.



****Next expected release****
- Friday 30/04/2021







