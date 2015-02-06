package soot.jimple.infoflow.util;

/**
 * Utility class for checking whether methods belong to system classes
 * 
 * @author Steven Arzt
 */
public class VMachineMethodHandler {
	
	/**
	 * Checks whether the given class name belongs to a system package
	 * @param className The class name to check
	 * @return True if the given class name belongs to a system package,
	 * otherwise false
	 */
	public static boolean isMethodInJVMStandard(String methodName) {
		return methodName.startsWith("<init>");
	}

}
