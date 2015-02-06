package a.org.trimps.susi.features;

import java.util.List;

import a.org.trimps.susi.IFeature;

import soot.jimple.infoflow.android.data.AndroidMethod;


public class ParameterContainsTypeOrNameFeature implements IFeature {

	private final String insideName;
	
	public ParameterContainsTypeOrNameFeature(String insideName) {
		this.insideName = insideName.toLowerCase();
	}
	
	@Override
	public Type applies(AndroidMethod method) {
		List<String> paramList = method.getParameters();
		for(String param : paramList){
			if(param.toLowerCase().contains(this.insideName))
				return Type.TRUE;
		}
		return Type.FALSE;
	}
	
	@Override
	public String toString() {
		return "<Parameter type contains " + this.insideName + ">";
	}

}
