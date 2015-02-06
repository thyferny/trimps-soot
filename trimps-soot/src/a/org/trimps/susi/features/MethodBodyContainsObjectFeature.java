package a.org.trimps.susi.features;

import soot.Body;
import soot.SootMethod;
import soot.jimple.infoflow.android.data.AndroidMethod;


public class MethodBodyContainsObjectFeature extends AbstractSootFeature {
	private final String objectName;
	
	public MethodBodyContainsObjectFeature(String androidJAR, String objectName){
		super(androidJAR);
		this.objectName = objectName.trim().toLowerCase();
	}
	
	@Override
	public Type appliesInternal(AndroidMethod method) {
		try {
			SootMethod sm = getSootMethod(method);
			if (sm == null) {
				System.err.println("Method not declared: " + method);
				return Type.NOT_SUPPORTED;
			}
			if (!sm.isConcrete())
				return Type.NOT_SUPPORTED;
			
			Body body = null;
			try{
				body = sm.retrieveActiveBody();
			}catch(Exception ex){
				return Type.NOT_SUPPORTED;
			}
			
			if(body.toString().toLowerCase().contains(objectName))
				return Type.TRUE;
			
//			for(Local local : sm.getActiveBody().getLocals())
//				if(local.getType().toString().trim().toLowerCase().contains(objectName)){
//					if(objectName.equals("android.location.LocationListener"))
//						System.out.println();
//					return Type.TRUE;
//				}

				return Type.FALSE;		
		}catch (Exception ex) {
			System.err.println("Something went wrong:");
			ex.printStackTrace();
			return Type.NOT_SUPPORTED;
		}
	}
	
	@Override
	public String toString() {
		return "Method-Body contains object '" + this.objectName;
	}
}
