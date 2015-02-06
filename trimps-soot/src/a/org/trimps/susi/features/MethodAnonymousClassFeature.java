package a.org.trimps.susi.features;

import java.util.regex.Pattern;

import a.org.trimps.susi.IFeature;

import soot.jimple.infoflow.android.data.AndroidMethod;


public class MethodAnonymousClassFeature implements IFeature {

	private final boolean anonymousClass;
	
	public MethodAnonymousClassFeature(boolean anonymousClass){
		this.anonymousClass = anonymousClass;
	}

	@Override
	public Type applies(AndroidMethod method) {
		int index = method.getClassName().lastIndexOf("$");

		if(index != -1){
			String subclassName = method.getClassName().substring(index+1);
			return (Pattern.matches("^\\d+$", subclassName)? Type.TRUE : Type.FALSE);
		}
		return Type.FALSE;
	}
	
	@Override
	public String toString() {
		return "<Method is part of a" + (anonymousClass ? "n anonymous" : " non-anonymous") +" class>";
	}

}
