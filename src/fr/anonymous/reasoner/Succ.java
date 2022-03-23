package fr.anonymous.reasoner;


import java.util.HashSet;
import java.util.Set;

public class Succ {
    //Startype s;
    Triple t;
    Set<Startype> Sset;
    public Succ( Triple t, Set<Startype> Sset) {
        this.t=t;
        this.Sset=Sset;
    }
    public Succ() {
        // TODO Auto-generated constructor stub
        this.t=new Triple();
        this.Sset=new HashSet<>();
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
