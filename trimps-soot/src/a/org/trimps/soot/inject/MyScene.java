package a.org.trimps.soot.inject;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import soot.SootClass;
import soot.SootFieldRef;

/**
 * 记录类成员变量，及其初始化类（暂时不包括静态类成员变量，静态类成员变量的实现是StaticFieldRef）
 * @author lixun
 *
 */
public class MyScene {
	
	private static MyScene instance = null;

	private Set<SootClass> scset = new HashSet<SootClass>();	//记录已经分析类成员变量的SootClass对象
	private Map<String, Set<SootFieldRef>> fieldMap = new HashMap<String, Set<SootFieldRef>>();	//记录SootClass对象包含的类成员
	private Set<SootFieldRef> fieldSet = new HashSet<SootFieldRef>();	//记录已经分析得到的类成员（包括静态的和动态的）
	private Map<SootFieldRef, Set<SootClass>> fieldImplMap = new HashMap<SootFieldRef, Set<SootClass>>();	//记录类成员有可能的实现类
	
	private List<Set<SootFieldRef>> identityFieldSet = new ArrayList<Set<SootFieldRef>>();
	
	private MyScene() {
		
	}
	
	public static MyScene v() {
		if(instance == null) {
			instance = new MyScene();
		}
		
		return instance;
	}
	
	public List<SootClass> getInstanceImpl(SootFieldRef sfr) {
		Set<SootClass> set = fieldImplMap.get(sfr);
		if(set == null) {
			return new ArrayList<SootClass>();
		}
		
		return new ArrayList<SootClass>(set);
	}
	
	public void addIdentityFieldRef(SootFieldRef ref1, SootFieldRef ref2) {
		for(Set<SootFieldRef> set : identityFieldSet) {
			if(set.contains(ref1) || set.contains(ref2)) {
				set.add(ref1);
				set.add(ref2);
				return ;
			}
		}
		
		Set<SootFieldRef> set = new HashSet<SootFieldRef>();
		set.add(ref1);
		set.add(ref2);
		identityFieldSet.add(set);
	}
	
	public void reorgnizeIdentityFieldRef() {
		for(Set<SootFieldRef> set : identityFieldSet) {
			Set<SootClass> allSet = new HashSet<SootClass>();
			for(SootFieldRef sfr : set) {
				Set<SootClass> subset = fieldImplMap.get(sfr);
				if(subset != null) {
					allSet.addAll(subset);
				}
			}
			
			for(SootFieldRef sfr : set) {
				fieldImplMap.put(sfr, allSet);
			}
		}
		
		identityFieldSet.clear();
	}
		
	public boolean addSootClass(SootClass sc) {
		return scset.add(sc);
	}
	
	public boolean addFieldSet(SootFieldRef field) {
		return fieldSet.add(field);
	}
	
	public void addSootFieldRef(SootClass sc, SootFieldRef field) {
		if(!fieldMap.containsKey(sc.getName())) {
			fieldMap.put(sc.getName(), new HashSet<SootFieldRef>());
		}
		
		fieldMap.get(sc.getName()).add(field);
		
		addFieldSet(field);
	}
	
	public void addFieldImplSootClass(SootFieldRef field, SootClass sc) {
		addFieldSet(field);
		if(!fieldImplMap.containsKey(field)) {
			fieldImplMap.put(field, new HashSet<SootClass>());
		}
		
		fieldImplMap.get(field).add(sc);
	}
}
