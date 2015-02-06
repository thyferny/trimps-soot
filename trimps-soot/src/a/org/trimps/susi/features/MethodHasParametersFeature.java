package a.org.trimps.susi.features;

import a.org.trimps.susi.IFeature;
import soot.jimple.infoflow.android.data.AndroidMethod;

public class MethodHasParametersFeature implements IFeature {

	public MethodHasParametersFeature(float weight) {
	}
	
	@Override
	public Type applies(AndroidMethod method) {
		return (method.getParameters().size() > 0 ? Type.TRUE : Type.FALSE);
	}
	
	@Override
	public String toString() {
		return "<Method has parameters>";
	}

}
