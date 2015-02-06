package a.org.trimps.susi.features;

import a.org.trimps.susi.IFeature;
import soot.jimple.infoflow.android.data.AndroidMethod;


public class MethodNameStartsWithFeature implements IFeature {

	private final String startsWith;
	
	public MethodNameStartsWithFeature(String startsWith, float weight) {
		this.startsWith = startsWith;
	}
	
	@Override
	public Type applies(AndroidMethod method) {
		return (method.getMethodName().startsWith(this.startsWith)? Type.TRUE : Type.FALSE);
	}
	
	@Override
	public String toString() {
		return "<Method name starts with " + this.startsWith + ">";
	}

}
