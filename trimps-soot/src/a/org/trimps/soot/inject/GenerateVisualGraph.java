package a.org.trimps.soot.inject;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.gephi.graph.api.DirectedGraph;
import org.gephi.graph.api.Edge;
import org.gephi.graph.api.GraphController;
import org.gephi.graph.api.GraphModel;
import org.gephi.graph.api.Node;
import org.gephi.io.exporter.api.ExportController;
import org.gephi.io.exporter.spi.GraphExporter;
import org.gephi.project.api.ProjectController;
import org.gephi.project.api.Workspace;
import org.openide.util.Lookup;

import soot.Body;
import soot.Local;
import soot.MethodOrMethodContext;
import soot.PatchingChain;
import soot.SootClass;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.infoflow.util.SystemClassHandler;
import soot.jimple.internal.IdentityRefBox;
import soot.jimple.internal.InvokeExprBox;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JSpecialInvokeExpr;
import soot.jimple.internal.JStaticInvokeExpr;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.internal.JimpleLocalBox;
import soot.jimple.internal.RValueBox;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.util.Chain;

public class GenerateVisualGraph {

	public static final String KEY_SRC_UNIT = "KEY_SRC_UNIT";
	public static final String KEY_CALL_TYPE = "KEY_CALL_TYPE";

	public static int CALL_TYPE_SYNC = 0x01;
	public static int CALL_TYPE_ASYNC = 0x02;

	private DirectedGraph directedGraph;
	private DoubleKeyMap<SootMethod, UnitGraph> unitMap = new DoubleKeyMap<SootMethod, UnitGraph>();
	protected boolean ignoreFlowsInSystemPackages = true;
	private String mOutputGraph;
	
	private static Map<String, Map<String,String>> SIGNATURE_MAP = new HashMap<String, Map<String,String>>();
	static{
		SIGNATURE_MAP.put("java.lang.Thread", new HashMap<String,String>(){{put("void start()","void run()");}});
		SIGNATURE_MAP.put("android.os.AsyncTask", new HashMap<String,String>(){{put("android.os.AsyncTask execute(java.lang.Object[])","java.lang.Object doInBackground(java.lang.Object[])");}});
//		SIGNATURE_MAP.put(key, value);
	}

	public void init(CallGraph cg,String mOutputGraph) {
		this.mOutputGraph = mOutputGraph;
		// Init a project - and therefore a workspace
		ProjectController pc = Lookup.getDefault().lookup(ProjectController.class);
		pc.newProject(); 
		Workspace workspace = pc.getCurrentWorkspace();

		// Get a graph model - it exists because we have a workspace
		GraphModel graphModel = Lookup.getDefault().lookup(GraphController.class).getModel();
		directedGraph = graphModel.getDirectedGraph();
		DoubleKeyMap<Node, MethodOrMethodContext> dkNode = new DoubleKeyMap<>();
		// Create nodes
		Iterator<MethodOrMethodContext> methodIterator = cg.sourceMethods();
		//将CallGraph中的调用者方法全部加入到有向图和dkNode缓存中
		while (methodIterator.hasNext()) {
			MethodOrMethodContext src = methodIterator.next();
			//TODO add async-possible node
			
			String className = src.method().getDeclaringClass().getName();
			if (ignoreFlowsInSystemPackages && SystemClassHandler.isClassInSystemPackage(className))
				continue;

			Node node = graphModel.factory().newNode(src.method().getName());
			node.getNodeData().setLabel(src.method().getName() + ":" + src.method().getDeclaringClass().toString());
			directedGraph.addNode(node);
			dkNode.add(node, src);
		}

		//从dkNode缓存出发，寻找有向图能够达到的节点，将此边的信息添加到有向图中，然后对可达节点进行缓存判断，如果不在缓存中，则放到map中，等遍历完成后统一添加到dkNode缓存中
		Map<MethodOrMethodContext, Node> map = new HashMap<MethodOrMethodContext, Node>();
		for (Node n1 : dkNode.key1()) {
			MethodOrMethodContext src = dkNode.getKey2(n1);
			Iterator<soot.jimple.toolkits.callgraph.Edge> edgeIterator = cg.edgesOutOf(src);
			//TODO analysis async node and add async edge
			while (edgeIterator.hasNext()) {
				soot.jimple.toolkits.callgraph.Edge sootEdge = edgeIterator.next();
				MethodOrMethodContext tgt = sootEdge.getTgt();
				String className = tgt.method().getDeclaringClass().getName();
				if (ignoreFlowsInSystemPackages && SystemClassHandler.isClassInSystemPackage(className))
					continue;
				Node n2 = dkNode.getKey1(tgt);
				if (n2 == null) {
					Node node = graphModel.factory().newNode(tgt.method().getName());
					node.getNodeData().setLabel(tgt.method().getName() + ":" + tgt.method().getDeclaringClass().toString());
					directedGraph.addNode(node);
					// dkNode.add(node, tgt);
					n2 = node;
					System.out.println("WARNING:Can not find " + tgt.toString() + " while " + sootEdge.toString());
					
//					//FIXME added by lixun	（暂时不用）
//					dkNode.add(n2, tgt);
					if(!map.containsKey(tgt)) {
						map.put(tgt, n2);
					}
				}

				Edge edge = graphModel.factory().newEdge(n1, n2, 1f, true);
				if (sootEdge.srcUnit() == null) {
					edge.getAttributes().setValue(KEY_CALL_TYPE, CALL_TYPE_ASYNC);
				} else {
					edge.getAttributes().setValue(KEY_CALL_TYPE, CALL_TYPE_SYNC);
					edge.getAttributes().setValue(KEY_SRC_UNIT, sootEdge.srcUnit().toString());
				}
				directedGraph.addEdge(edge);
			}
		}
		
		while(!map.isEmpty()) {
			Map<MethodOrMethodContext, Node> map2 = new HashMap<MethodOrMethodContext, Node>();
			Iterator<MethodOrMethodContext> mit = map.keySet().iterator();
			while(mit.hasNext()) {
				MethodOrMethodContext momc = mit.next();
				Node n1 = map.get(momc);
				
				dkNode.add(n1, momc);
				
				Iterator<soot.jimple.toolkits.callgraph.Edge> edgeIterator = cg.edgesOutOf(momc);
				//TODO analysis async node and add async edge
				while (edgeIterator.hasNext()) {
					soot.jimple.toolkits.callgraph.Edge sootEdge = edgeIterator.next();
					MethodOrMethodContext tgt = sootEdge.getTgt();
					String className = tgt.method().getDeclaringClass().getName();
					if (ignoreFlowsInSystemPackages && SystemClassHandler.isClassInSystemPackage(className))
						continue;
					Node n2 = dkNode.getKey1(tgt);
					if (n2 == null) {
						Node node = graphModel.factory().newNode(tgt.method().getName());
						node.getNodeData().setLabel(tgt.method().getName() + ":" + tgt.method().getDeclaringClass().toString());
						directedGraph.addNode(node);
						// dkNode.add(node, tgt);
						n2 = node;
						System.out.println("WARNING:Can not find " + tgt.toString() + " while " + sootEdge.toString());
						
						if(!map2.containsKey(tgt)) {
							map2.put(tgt, n2);
						}
					}

					Edge edge = graphModel.factory().newEdge(n1, n2, 1f, true);
					if (sootEdge.srcUnit() == null) {
						edge.getAttributes().setValue(KEY_CALL_TYPE, CALL_TYPE_ASYNC);
					} else {
						edge.getAttributes().setValue(KEY_CALL_TYPE, CALL_TYPE_SYNC);
						edge.getAttributes().setValue(KEY_SRC_UNIT, sootEdge.srcUnit().toString());
					}
					directedGraph.addEdge(edge);
				}
			}
			
			map = map2;
		}
		
		//FIXME added by lixun(给我们自己的图添加额外的边，与Soot的Callgraph无关)
//		for(Node n1 : dkNode.key1()) {
//			MethodOrMethodContext src = dkNode.getKey2(n1);
//			Iterator<soot.jimple.toolkits.callgraph.Edge> edgeIterator = cg.edgesOutOf(src);
//			//TODO analysis async node and add async edge	（暂时不用）
//			while (edgeIterator.hasNext()) {
//				soot.jimple.toolkits.callgraph.Edge sootEdge = edgeIterator.next();
//				MethodOrMethodContext tgt = sootEdge.getTgt();
//				String className = tgt.method().getDeclaringClass().getName();
//				if (ignoreFlowsInSystemPackages && SystemClassHandler.isClassInSystemPackage(className))
//					continue;
//				
//				scanMethodForAsyncCall(tgt.method(), dkNode, graphModel);	
//			}
//		}

		for (Node n1 : dkNode.key1()) {
			SootMethod src = dkNode.getKey2(n1).method();
			if(!src.method().hasActiveBody()) {
				src.method().retrieveActiveBody();
			}
			
			if(!src.method().hasActiveBody()) {
				System.out.println("Count not retrieve ActiveBody of Method: " + src.method());
				continue;
			}
			
			BriefUnitGraph unitGraph = new BriefUnitGraph(src.method().getActiveBody());
//			handleUnitGraph(unitGraph) //TODO
			unitMap.add(src,unitGraph);
		}

//		handleLocalAsyncCall(cg);	//TODO 暂时不用
		// Count nodes and edges
		System.out.println("Nodes: " + directedGraph.getNodeCount() + " Edges: " + directedGraph.getEdgeCount());

		saveGraph(workspace,mOutputGraph);
	}

	private void handleLocalAsyncCall(CallGraph cg) {
//		soot.jimple.toolkits.callgraph.Edge e=new soot.jimple.toolkits.callgraph.Edge(src, srcUnit, tgt);
		for(UnitGraph uGraph:unitMap.key2()){	//依次分析每一个方法
			Body body = uGraph.getBody();
			/*
			List<Local> paras = body.getParameterLocals();
			Chain<Local> locals = body.getLocals();
			List<Value> ref = body.getParameterRefs();
//			System.out.println(uGraph.getBody()+"\n");
			IdentityRefBox lastIdentityRefBox = null;//java compile right to left
			for(Local lc:locals){//for each exp
//				System.out.println(lc);
//				if(vb instanceof IdentityRefBox){
//					lastIdentityRefBox = (IdentityRefBox)vb;
//				}
//				if(vb instanceof JimpleLocalBox){
//					JimpleLocalBox thisJimple = (JimpleLocalBox)vb;
//					if(!mapWithKey(localMap,thisJimple)){
//						if(lastIdentityRefBox==null){
//							System.err.println("Error:can not find the def type of the jimple:"+thisJimple);
//						}else{
//							localMap.put(thisJimple, lastIdentityRefBox);
//						}
//					}
//				}
//				if(vb instanceof VariableBox){
//					System.out.println(vb);
//				}
			}
//			System.out.println("-----------------------------------");
			int size = ref.size();
			Local[] lcArray = locals.toArray(new Local[size]);
			for(int i=0;i<size;i++){//default parameter~not a link here...defined in context 
//				System.out.print(paras.get(i).getType());
//				System.err.print(" link 0 with the instance of ");
//				System.out.println(lcArray[i].getType());
			} */
			List<ValueBox> useAndDef = body.getUseAndDefBoxes();	//获取方法内所有使用和定义的变量
			List<Unit> clone = new ArrayList<Unit>();
			//JimpleLocalBox, IdentityRefBox, JAssignStmt$LinkedRValueBox, JAssignStmt$LinkedVariableBox, ImmediateBox, InvokeExprBox
			
			PatchingChain<Unit> units = body.getUnits();
			for(Unit u:units){
				clone.add(u);
			}
			for(ValueBox vb:useAndDef){
				Stmt stmt = findVbInUnits(clone,vb);	//找到函数体中使用ValueBox的地方
				if(vb instanceof RValueBox){	//
					handleRValueBox(cg, uGraph, vb, stmt);
				}else if(vb instanceof InvokeExprBox){	//
					handleInvokeExprBox(cg, uGraph, vb, stmt);
				}
			}
			System.out.println("-----------------------------------");
		}
	}

	private void handleInvokeExprBox(CallGraph cg, UnitGraph uGraph,
			ValueBox vb, Stmt stmt) {
		InvokeExprBox rvb = (InvokeExprBox)vb;
		Value val = rvb.getValue();
		if(val instanceof JSpecialInvokeExpr){//link a static method with variable as args' type and it's return type
			JSpecialInvokeExpr jSpecialInvokeExpr = (JSpecialInvokeExpr)val;
			SootMethod baseMethod = jSpecialInvokeExpr.getMethod();
			SootClass invokeClass = jSpecialInvokeExpr.getMethodRef().declaringClass();
			SootMethod tgt = findTargetMethod(invokeClass,baseMethod);
			for(int i=0;i<jSpecialInvokeExpr.getArgCount();i++){
				Value arg = jSpecialInvokeExpr.getArg(i);
				System.out.print(baseMethod);
				System.err.print(" link 4 with the instance of ");
				System.out.println(arg.getType());
				if(tgt!=null){
					soot.jimple.toolkits.callgraph.Edge e=new soot.jimple.toolkits.callgraph.Edge(unitMap.getKey1(uGraph), stmt, tgt);//TODO where is the tgt for async?
					cg.addEdge(e);
				}
			}
		}else if(val instanceof JVirtualInvokeExpr){//link a method with variable as args' type and it's return type
			JVirtualInvokeExpr jVirtualInvokeExpr = ((JVirtualInvokeExpr)val);
			SootMethod baseMethod = jVirtualInvokeExpr.getMethod();
			Type baseType = val.getType();
			SootClass invokeClass = jVirtualInvokeExpr.getMethodRef().declaringClass();
			SootMethod tgt = findTargetMethod(invokeClass,baseMethod);
			for(int i=0;i<jVirtualInvokeExpr.getArgCount();i++){
				Value arg = jVirtualInvokeExpr.getArg(i);
				System.out.print(baseMethod);
				System.err.print(" link 1 with the instance of ");
				System.out.println(arg.getType());
				if(tgt!=null){
					soot.jimple.toolkits.callgraph.Edge e=new soot.jimple.toolkits.callgraph.Edge(unitMap.getKey1(uGraph), stmt, tgt);//TODO where is the tgt for async?
					cg.addEdge(e);
				}
			}
		}
		else if(val instanceof JInstanceFieldRef){//link a instance's variable and the return type
			Type srcType = ((JInstanceFieldRef)val).getBase().getType();
			Type tgtType = ((JInstanceFieldRef)val).getType();
			System.out.print(srcType);
			System.err.print(" link 2 with the instance of ");
			System.out.println(tgtType);
//						soot.jimple.toolkits.callgraph.Edge e=new soot.jimple.toolkits.callgraph.Edge(baseMethod, vb, unitMap.getKey1(uGraph));//TODO what is the src method..
//						cg.addEdge(e);
		}
		else if(val instanceof JStaticInvokeExpr){//link a static method with variable as args' type and it's return type
			JStaticInvokeExpr jStaticInvokeExpr = (JStaticInvokeExpr)val;
			SootMethod baseMethod = jStaticInvokeExpr.getMethod();
			SootClass invokeClass = jStaticInvokeExpr.getMethodRef().declaringClass();
			SootMethod tgt = findTargetMethod(invokeClass,baseMethod);
			for(int i=0;i<jStaticInvokeExpr.getArgCount();i++){
				Value arg = jStaticInvokeExpr.getArg(i);
				System.out.print(baseMethod);
				System.err.print(" link 3 with the instance of ");
				System.out.println(arg.getType());
				if(tgt!=null){
					soot.jimple.toolkits.callgraph.Edge e=new soot.jimple.toolkits.callgraph.Edge(unitMap.getKey1(uGraph), stmt, tgt);//TODO where is the tgt for async?
					cg.addEdge(e);
				}
			}
		}
	}

	private SootMethod findTargetMethod(SootClass invokeClass,SootMethod baseMethod) {
		SootMethod tgt = null;
		String subSignature = baseMethod.getSubSignature();
		List<SootClass> realClassHierarchy = new ArrayList<SootClass>();
		SootClass superClass = invokeClass;
		while(superClass!=null){
			realClassHierarchy.add(superClass);
			if(superClass.hasSuperclass()){
				superClass = superClass.getSuperclass();
			}else{
				superClass=null;
			}
		}
		
		for(String key:SIGNATURE_MAP.keySet()){
			if(canFindSootClass(realClassHierarchy,key)){
				for(String fromMethod:SIGNATURE_MAP.get(key).keySet()){
					if(subSignature.equals(fromMethod)){
						String toMethod = SIGNATURE_MAP.get(key).get(fromMethod);
						tgt = invokeClass.getMethod(toMethod);
						System.err.println("find async call "+fromMethod);
					}
				}
			}
		}
		return tgt;
	}

	private boolean canFindSootClass(List<SootClass> realClassHierarchy,
			String key) {
		for(SootClass sc:realClassHierarchy){
			if(sc.getName().equals(key)){
				return true;
			}
		}
		return false;
	}

	private void handleRValueBox(CallGraph cg, UnitGraph uGraph, ValueBox vb,
			Stmt stmt) {
		RValueBox rvb = (RValueBox)vb;
//					System.out.println(rvb.getValue());
		Value val = rvb.getValue();
		if(val instanceof JNewExpr){//new
			JNewExpr jNewExpr = ((JNewExpr)val);
//						System.out.println("new "+jNewExpr.getType());
		}
	}

	private Stmt findVbInUnits(Collection<Unit> units, ValueBox vb) {
		for(Unit u:units){
			for(ValueBox ivb:u.getUseBoxes()){
				if(ivb.getValue().equals(vb.getValue())){
					return (Stmt) u;
				};
			}
//			u.getJavaSourceStartLineNumber()==vb.getJavaSourceStartLineNumber()){
//				
//			}
		}
		return null;
	}

	private boolean mapWithKey(Map<JimpleLocalBox, IdentityRefBox> localMap,
			JimpleLocalBox thisJimple) {
		for(JimpleLocalBox jl:localMap.keySet()){
			if(((JimpleLocal)jl.getValue()).getName().equals(((JimpleLocal)thisJimple.getValue()).getName())){
				return true;
			}
		}
		return false;
	}

	private void saveGraph(Workspace workspace, String outputGraph) {
		ExportController ec = Lookup.getDefault().lookup(ExportController.class);
		GraphExporter exporter = (GraphExporter) ec.getExporter("gexf"); 
		exporter.setExportVisible(true);
		exporter.setWorkspace(workspace);
		try {
			ec.exportFile(new File(outputGraph), exporter);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	/**
	 * ����ָ���ķ������룬�������õ����½ڵ���±߼��뵽dkNode��directedGraph��
	 * @param m
	 * @param dkNode
	 */
	private void scanMethodForAsyncCall(SootMethod m, DoubleKeyMap<Node, MethodOrMethodContext> dkNode, GraphModel graphModel) {
		if (m.hasActiveBody()) {
			// Check whether this is a system class we need to ignore
			final String className = m.getDeclaringClass().getName();

			// Look for a source in the method. Also look for sinks. If we
			// have no sink in the program, we don't need to perform any
			// analysis
			PatchingChain<Unit> units = m.getActiveBody().getUnits();
			for (Unit u : units) {
				Stmt s = (Stmt) u;
				if (s instanceof JInvokeStmt) {
					JInvokeStmt invokeStmt = (JInvokeStmt) s;
					ValueBox vb = invokeStmt.getInvokeExprBox();
					InvokeExpr ie = invokeStmt.getInvokeExpr();
					if (vb instanceof InvokeExprBox) {

					}
					if (ie instanceof JVirtualInvokeExpr) {
						SootMethodRef ref = ((JVirtualInvokeExpr) ie).getMethodRef();
						if (ref.getSubSignature().getString().equals("android.os.AsyncTask execute(java.lang.Object[])")) {
							SootClass sc = ref.declaringClass();
							boolean declareDoInBackGroud = sc.declaresMethod("java.lang.Object doInBackground(java.lang.Object[])");
							boolean declareOnPostExecute = sc.declaresMethod("void onPostExecute(java.lang.Object)");
							boolean declareOnPreExecute = sc.declaresMethod("void onPreExecute()");

							SootMethod doInBackground = null;
							if (declareDoInBackGroud) {
								doInBackground = sc.getMethod("java.lang.Object doInBackground(java.lang.Object[])");
							}

							SootMethod onPostExecute = null;
							if (declareOnPostExecute) {
								onPostExecute = sc.getMethod("void onPostExecute(java.lang.Object)");
							}

							SootMethod onPreExecute = null;
							if (declareOnPreExecute) {
								onPreExecute = sc.getMethod("void onPreExecute()");
							}
							
							Node sourceNode = dkNode.getKey1(m);
							
							if(declareDoInBackGroud) {
								boolean containInBackGroud = dkNode.containKey2(doInBackground);
								
								Node n2 = null;
								if(!containInBackGroud) {
									Node node = graphModel.factory().newNode(doInBackground.getName());
									node.getNodeData().setLabel(doInBackground.getName() + ":" + doInBackground.getDeclaringClass().toString());
									directedGraph.addNode(node);
									n2=node;
									System.out.println("WARNING:Can not find " + doInBackground.toString() + " while " + doInBackground.toString());
//									dkNode.add(node, doInBackground);
								}
								
//								n2 = dkNode.getKey1(doInBackground);
								if(n2!=null){
								Edge edge = graphModel.factory().newEdge(sourceNode, n2, 1f, true);
								edge.getAttributes().setValue(KEY_CALL_TYPE, CALL_TYPE_ASYNC);
								directedGraph.addEdge(edge);
								}
							}
							
							if(declareOnPreExecute) {
								boolean containDoPreExecute = dkNode.containKey2(onPreExecute);
								
								Node n2 = null;
								if(!containDoPreExecute) {
									Node node = graphModel.factory().newNode(onPreExecute.getName());
									node.getNodeData().setLabel(onPreExecute.getName() + ":" + onPreExecute.getDeclaringClass().toString());
									directedGraph.addNode(node);
									n2=node;
									System.out.println("WARNING:Can not find " + onPreExecute.toString() + " while " + onPreExecute.toString());
//									dkNode.add(node, onPreExecute);
								}
								
//								n2 = dkNode.getKey1(onPreExecute);
								if(n2!=null){
								Edge edge = graphModel.factory().newEdge(sourceNode, n2, 1f, true);
								edge.getAttributes().setValue(KEY_CALL_TYPE, CALL_TYPE_ASYNC);
								directedGraph.addEdge(edge);
								}
							}
							
							if(declareOnPostExecute) {
								boolean containDoPostExecute = dkNode.containKey2(onPostExecute);
								Node n2 = null;
								if(!containDoPostExecute) {
									Node node = graphModel.factory().newNode(onPostExecute.getName());
									node.getNodeData().setLabel(onPostExecute.getName() + ":" + onPostExecute.getDeclaringClass().toString());
									directedGraph.addNode(node);
									n2=node;
									System.out.println("WARNING:Can not find " + onPostExecute.toString() + " while " + onPostExecute.toString());
//									dkNode.add(node, onPostExecute);
								}
								
//								n2 = dkNode.getKey1(onPostExecute);
								if(n2!=null){
									Edge edge = graphModel.factory().newEdge(sourceNode, n2, 1f, true);
									edge.getAttributes().setValue(KEY_CALL_TYPE, CALL_TYPE_ASYNC);
									directedGraph.addEdge(edge);
								}
							}
							// we can link this three method together
						}
					}
				}
			}

		}
	}
}