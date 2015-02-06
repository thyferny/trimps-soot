package a.org.trimps.susi.features;

import a.org.trimps.susi.IFeature;
import soot.jimple.infoflow.android.data.AndroidMethod;

public class MethodClassContainsNameFeature implements IFeature {

	private final String partOfName;
	
	public MethodClassContainsNameFeature(String partOfName){
		this.partOfName = partOfName.toLowerCase();
	}

	@Override
	public Type applies(AndroidMethod method) {
		return (method.getClassName().toLowerCase().contains(partOfName)? Type.TRUE : Type.FALSE);
	}
	
	@Override
	public String toString() {
		return "<Method is part of class that contains the name " + partOfName + ">";
	}
}
