package fr.anonymous.reasoner;

public class IndexedStartype {
    private Startype s;
    private int id;

    public IndexedStartype(Startype st, int id) {
        this.s=st;
        this.id=id;
    }

    public Startype getS() {
        return s;
    }

    public void setS(Startype s) {
        this.s = s;
    }

    public int getId() {
        return id;
    }

    public void setId(int id) {
        this.id = id;
    }
}
