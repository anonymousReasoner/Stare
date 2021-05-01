package fr.anonymous.reasoner;

public class StartypePair {
	Startype firstStar;
	Startype secondStar;
	public StartypePair() {

	}
	public StartypePair(Startype firstStar,Startype secondStar ) {
		this.firstStar=firstStar;
		this.secondStar=secondStar;
	}
	public Startype getFirstStar() {
		return firstStar;
	}
	public void setFirstStar(Startype firstStar) {
		this.firstStar = firstStar;
	}
	public Startype getSecondStar() {
		return secondStar;
	}
	public void setSecondStar(Startype secondStar) {
		this.secondStar = secondStar;
	}

}
