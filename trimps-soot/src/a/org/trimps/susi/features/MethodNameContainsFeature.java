package a.org.trimps.susi.features;

import a.org.trimps.susi.IFeature;
import soot.jimple.infoflow.android.data.AndroidMethod;


public class MethodNameContainsFeature implements IFeature {

	private final String endsWith;
	
	public MethodNameContainsFeature(String endsWith) {
		this.endsWith = endsWith.toLowerCase();
	}

	@Override
	public Type applies(AndroidMethod method) {
		return (method.getMethodName().toLowerCase().contains(endsWith) ? Type.TRUE : Type.FALSE);
	}
	
	@Override
	public String toString() {
		return "<Method name contains " + this.endsWith + ">";
	}

}
