package a.org.trimps.susi.features;

import a.org.trimps.susi.IFeature;
import soot.jimple.infoflow.android.data.AndroidMethod;


public class VoidOnMethodFeature implements IFeature {

	public VoidOnMethodFeature() {
	}
	

	@Override
	public Type applies(AndroidMethod method) {
		return (method.getMethodName().startsWith("on") && 
				(method.getReturnType().toString().equals("void")
						|| method.getReturnType().toString().equals("boolean"))? Type.TRUE : Type.FALSE);
	}
	
	@Override
	public String toString() {
		return "<Method starts with on and has void/bool return type>";
	}

}
