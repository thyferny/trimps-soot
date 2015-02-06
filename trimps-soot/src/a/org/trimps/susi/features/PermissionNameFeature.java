package a.org.trimps.susi.features;

import a.org.trimps.susi.IFeature;
import soot.jimple.infoflow.android.data.AndroidMethod;

public class PermissionNameFeature implements IFeature {

	private final String permission;
	
	public PermissionNameFeature(String permission) {
		if(permission.contains("."))
			this.permission = permission.substring(permission.lastIndexOf(".") + 1);
		else
			this.permission = permission;
	}
	
	@Override
	public Type applies(AndroidMethod method) {
		for (String perm : method.getPermissions()) {
			String stripped = perm;
			if (stripped.contains("."))
				stripped = perm.substring(perm.lastIndexOf(".") + 1);
			if (stripped.equals(this.permission))
				return Type.TRUE;
		}
		return Type.FALSE;
	}
	
	@Override
	public String toString() {
		return "<Permission name is " + this.permission + ">";
	}
	
	@Override
	public boolean equals(Object other) {
		if (super.equals(other))
			return true;
		if (!(other instanceof PermissionNameFeature))
			return false;
		PermissionNameFeature pnf = (PermissionNameFeature) other;
		return pnf.permission.equals(this.permission);
	}
	
	@Override
	public int hashCode() {
		return this.permission.hashCode();
	}

}
