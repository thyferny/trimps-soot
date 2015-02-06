package a.org.trimps.susi.features;

import a.org.trimps.susi.IFeature;
import soot.jimple.infoflow.android.data.AndroidMethod;


public class MethodNameEndsWithFeature implements IFeature {

	private final String endsWith;
	
	public MethodNameEndsWithFeature(String endsWith) {
		this.endsWith = endsWith;
	}

	@Override
	public Type applies(AndroidMethod method) {
		String methodNameLowerCase = method.getMethodName().toLowerCase();
		String endsWithLowerCase = endsWith.toLowerCase();
		return (methodNameLowerCase.endsWith(endsWithLowerCase)? Type.TRUE : Type.FALSE);
	}
	
	@Override
	public String toString() {
		return "<Method name ends with " + this.endsWith + ">";
	}

}
