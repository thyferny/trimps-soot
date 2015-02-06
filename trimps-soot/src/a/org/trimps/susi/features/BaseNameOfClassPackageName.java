package a.org.trimps.susi.features;

import a.org.trimps.susi.IFeature;
import soot.jimple.infoflow.android.data.AndroidMethod;


public class BaseNameOfClassPackageName implements IFeature {
	private final String baseNameOfClassPackageName;
	
	public BaseNameOfClassPackageName(String baseNameOfClassPackageName){
		this.baseNameOfClassPackageName = baseNameOfClassPackageName;
	}
	
	@Override
	public Type applies(AndroidMethod method) {
		String[] classNameParts = method.getClassName().split(".");
		if(classNameParts.length>2){
			String otherBaseNameOfClassPackageName = classNameParts[classNameParts.length -2];
			return (otherBaseNameOfClassPackageName.equals(baseNameOfClassPackageName) ? Type.TRUE : Type.FALSE);
		}else{
			return Type.FALSE;
		}
		
	}
	
	@Override
	public String toString() {
		return "<Base name of class package name: " + baseNameOfClassPackageName + ">";
	}
}
