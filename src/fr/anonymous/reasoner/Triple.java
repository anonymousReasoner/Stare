/*
 * $Id$
 *
 * Copyright (C) Paris8-Paris13, 2013-2021
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA
 */

package fr.anonymous.reasoner;

/*
 * $Id$
 *
 * Copyright (C) Paris8-Paris13, 2013-2021
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA
 */


import org.semanticweb.owlapi.manchestersyntax.renderer.ManchesterOWLSyntaxOWLObjectRendererImpl;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLPropertyExpression;

import java.io.PrintWriter;
import java.io.Serializable;
import java.util.Set;

// A triple of a startype. It consists of (core, ridge, tip)

public class Triple implements Serializable {
    //for display
    //private int idT = 0;
    //private int matchedIdT = 0;
    //private String matchedContent = null;
    //private String matchedStIDs = null;
    //private String stIDs = null;
    //The hashCode is not immutable since Ray is not immutable. Therefore, each object should not be changed if it is hashed in a structure
    // To simplify computation of hashCode of startype, we do not add core ID to triple ID
    private int hashcode = 0;
    private   int idT=0;
    public int getIdT() {
		return idT;
	}

	public void setIdT(int idT) {
		this.idT = idT;
	}

	private ConceptLabel core;
    private Set<OWLIndividual> coreI;
    private Ray ray;
    //private int counter = 0;

    public Triple() {
        this.core = new ConceptLabel();
        this.ray = new Ray();
        hashcode = sumCode();
    }

    //Create a ray when we know ids
    public Triple(ConceptLabel c, Ray r) {
        this.core = new ConceptLabel(c);
        this.ray = new Ray(r.getRidge(), r.getTip());
        hashcode = sumCode();
    }

    //Clones
    public Triple(Triple tr) {
        this.core = new ConceptLabel(tr.getCore().getConcepts());
        this.ray = new Ray(tr.getRay().getRidge().getRoles(), tr.getRay().getTip().getConcepts());
        hashcode = sumCode();
    }

    /*
     * Changes directly the core
     */
    public Triple addConceptsToCore(Set<OWLClassExpression> freshes) {
        this.core.addAll(freshes);
        hashcode = sumCode();
        return this;
    }

    /*
     * Changes directly the tip
     */
    public Triple addConceptsToRay(Set<OWLClassExpression> freshes) {
        this.ray.addConcepts(freshes);
        hashcode = sumCode();
        return this;
    }

    /*
     * Changes directly the ridge
     */
    public Triple addRolesToRay(Set<OWLPropertyExpression> rs) {
        this.ray.addRoles(rs);
        hashcode = sumCode();
        return this;
    }

    public boolean isInverseOf(ConceptLabel co, Ray ray, ReasoningData data) {
        if (!this.core.equals(ray.getTip()))
            return false;
        if (!ray.getTip().equals(this.core))
            return false;
        if (!this.ray.getRidge().isInverseOf(ray.getRidge()))
            return false;
        else
            return true;
    }

    public Triple getInverseOf() {
        return new Triple(this.getRay().getTip(),
                new Ray(this.getRay().getRidge().getInverseOf(), this.getCore()));
    }

    public Triple merge(Triple tr) {
        Ray newr = new Ray(tr.getRay().getRidge(), tr.getRay().getTip());
        newr.addConcepts(this.getRay().getTip().getConcepts());
        newr.addRoles(this.getRay().getRidge().getRoles());
        Triple newTr = new Triple(tr.getCore(), newr);
        newTr.addConceptsToCore(this.getCore().getConcepts());
        return newTr;
    }

    //The core, ridge, tip of this contains the core, ridge, tip of "tr"
    public boolean containsAll(Triple tr) {
        if (this.core.containsAll(tr.getCore()) &&
                this.ray.containsAll(tr.getRay()))
            return true;
        else
            return false;
    }

    public Ray getRay() {
        return this.ray;
    }

    public Triple setRay(Ray r) {
        this.ray = r;
        hashcode = sumCode();
        return this;
    }

    public ConceptLabel getCore() {
        return this.core;
    }

    public Triple setCore(ConceptLabel id) {
        this.core = id;
        hashcode = sumCode();
        return this;
    }

    /*
     * not commutative
     */
    public int sumCode() {
        long hash = 1234;
        hash += this.ray.hashCode();
        hash += this.getCore().hashCode();
        return (int) (hash);
    }

    @Override
    public int hashCode() {
        return hashcode;
    }

    @Override
    public boolean equals(Object obj) {
        //System.out.println("ENterring ... EQUALs");
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        Triple other = (Triple) obj;
        if (!this.getCore().equals(other.getCore())) {
            //System.out.println("TR Core EQUAL FALSE = "+ this.getCore().toString()+ "<>"+ other.getCore().toString());
            return false;
        }
        if (!this.getRay().equals(other.getRay())) {
            //System.out.println("TR Core EQUAL FALSE = "+ this.getRay().toString()+ "<>"+ other.getRay().toString());
            return false;
        }
        //System.out.println("TRIPLE EQUAL TRUE");
        return true;
    }

    public String toSimpleString() {
        String s = this.getCore().toSimpleString() + "hashcode=" + hashcode + ", " + this.getRay().getRidge().toSimpleString() + "-" + this.getRay().getTip().toSimpleString();
        return s;
    }

    public void toXML(PrintWriter writer) {

        ManchesterOWLSyntaxOWLObjectRendererImpl render = new ManchesterOWLSyntaxOWLObjectRendererImpl();
        writer.print("<triple> hashcode =" + hashcode);
        //writer.print("<core>\n");
        this.getCore().toXML(writer);
        writer.print(" - ");
        //writer.print("</core>\n");
        //writer.print("<ridge>\n");
        this.getRay().getRidge().toXML(writer);
        writer.print(" - ");
        //writer.print("</ridge>\n");
        //writer.print("<tip>\n");
        this.getRay().getTip().toXML(writer);
        //writer.print(", STIDs = " + this.getStIDs());
        //writer.print("</triple>\n");
        //writer.print("<inv-triple> hashcode = "+this.getMatchedIdT() +", content= " +this.getMatchedContent()+ ", STIDS = "+this.getMatchedStIDs()+" ");

        writer.print("</inv-triple>\n");
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("\nTriple: hashcode=" + hashcode + System.getProperty("line.separator"));
        sb.append(core.toString());
        sb.append("Ray:" + System.getProperty("line.separator"));
        sb.append(ray.toString());

        return sb.toString();
    }

    public Set<OWLIndividual> getCoreI() {
        return coreI;
    }

    public void setCoreI(Set<OWLIndividual> coreI) {
        this.coreI = coreI;
    }


}
