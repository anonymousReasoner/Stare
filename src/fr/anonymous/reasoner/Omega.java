package fr.anonymous.reasoner;


import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class Omega {
    Startype s;
    Triple t;
    Set<Startype> Sset;
    public Omega(Startype s, Triple t) {
        this.s=s;
        this.t=t;
        this.Sset=new HashSet<Startype>();
    }
    public Omega() {
        // TODO Auto-generated constructor stub
        this.Sset=new HashSet<Startype>();
    }
    public Startype getS() {
        return s;
    }
    public void setS(Startype s) {
        this.s = s;
    }
    public Triple getT() {
        return t;
    }
    public void setT(Triple t) {
        this.t = t;
    }
    public Set<Startype> getSset() {
        return Sset;
    }
    public void setSset(Set<Startype> sset) {
        Sset = sset;
    }

}
