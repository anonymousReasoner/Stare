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


import java.io.Serializable;

/**
 * Representation of a role. Each role has a name and an identifier, that are
 * different for the roles of the ontology. The roles can also be transitive,
 * functional, inverse or transitive closures.<br/>
 * <p>
 * An inverse role will have the same name and the same properties (functional,
 * transitive), but an identifier negative. A transitive closure role will have
 * the same name, a negative identifier and will never be functional (of course,
 * it will be transitive. A negative transitive closure is a transitive closure
 * with the isInverse variable set at true.set at true.<br/>
 * <p>
 * Transitive closures, inverses and inverse transitive closures are
 * automatically generated by methods of the LoadOntology classes and will be
 * initialized with an identifier value of -2.
 *
 * @author Jeremy Lhez
 */
public class RoleAttributes implements Serializable {
    protected boolean isTransitive;
    protected boolean isFunctional;
    protected boolean isInverse;
    protected boolean isTransitiveClosure;
    protected boolean isData;

    public RoleAttributes(boolean func, boolean inv, boolean data, boolean trans, boolean transClosure) {
        this.isTransitiveClosure = transClosure;
        this.isTransitive = trans;
        this.isInverse = inv;
        this.isFunctional = func;
        this.isData = data;
    }


    public boolean isData() {
        return isData;
    }

    public void setData(boolean v) {
        this.isData = v;
    }


    public boolean isTransitive() {
        return isTransitive;
    }

    public void setTransitive(boolean v) {
        this.isTransitive = v;
    }

    public boolean isTransitiveClosure() {
        return isTransitiveClosure;
    }

    public void setTransitiveClosure(boolean v) {
        this.isTransitiveClosure = v;
    }

    public boolean isFunctional() {
        return isFunctional;
    }

    public void setFunctional(boolean v) {
        this.isFunctional = v;
    }


    public boolean isInverse() {
        return isInverse;
    }

    public void setInverse(boolean value) {
        this.isInverse = value;
    }
}
