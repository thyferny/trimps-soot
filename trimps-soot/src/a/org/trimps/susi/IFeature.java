package a.org.trimps.susi;

import soot.jimple.infoflow.android.data.AndroidMethod;


public interface IFeature {
	
	enum Type{TRUE, FALSE, NOT_SUPPORTED}
	
	Type applies(AndroidMethod method);
	
	String toString();
	
}
