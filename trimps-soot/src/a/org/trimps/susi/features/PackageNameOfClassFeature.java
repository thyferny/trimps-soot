package a.org.trimps.susi.features;

import a.org.trimps.susi.IFeature;
import soot.jimple.infoflow.android.data.AndroidMethod;


public class PackageNameOfClassFeature implements IFeature {
	private final String packageNameOfClass;
	
	public PackageNameOfClassFeature(String packageNameOfClass, float weight){
		this.packageNameOfClass = packageNameOfClass;
	}

	@Override
	public Type applies(AndroidMethod method) {
		String otherPackageNameOfClass = method.getClassName().substring(0, method.getClassName().lastIndexOf("."));
		
		return (otherPackageNameOfClass.equals(packageNameOfClass) ? Type.TRUE : Type.FALSE);
	}
	
	@Override
	public String toString() {
		return "<Package path of method class-name is: " + packageNameOfClass + ">";
	}
}
