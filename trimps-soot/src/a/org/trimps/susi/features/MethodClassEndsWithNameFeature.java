package a.org.trimps.susi.features;

import a.org.trimps.susi.IFeature;
import soot.jimple.infoflow.android.data.AndroidMethod;

public class MethodClassEndsWithNameFeature implements IFeature {

	private final String partOfName;
	
	public MethodClassEndsWithNameFeature(String partOfName){
		this.partOfName = partOfName;
	}
	
	@Override
	public Type applies(AndroidMethod method) {
		return (method.getClassName().endsWith(partOfName)? Type.TRUE : Type.FALSE);
	}
	
	@Override
	public String toString() {
		return "<Method is part of class that ends with " + partOfName + ">";
	}
}
