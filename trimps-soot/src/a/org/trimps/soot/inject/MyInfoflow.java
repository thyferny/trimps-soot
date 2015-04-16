/*******************************************************************************
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the GNU Lesser Public License v2.1
 * which accompanies this distribution, and is available at
 * http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
 * 
 * Contributors: Christian Fritz, Steven Arzt, Siegfried Rasthofer, Eric
 * Bodden, and others.
 ******************************************************************************/
package a.org.trimps.soot.inject;

import heros.solver.CountingThreadPoolExecutor;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.TimeUnit;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Body;
import soot.MethodOrMethodContext;
import soot.PackManager;
import soot.PatchingChain;
import soot.PointsToAnalysis;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootFieldRef;
import soot.SootMethod;
import soot.Transform;
import soot.Unit;
import soot.UnitBox;
import soot.Value;
import soot.ValueBox;
import soot.jimple.InvokeExpr;
import soot.jimple.ParameterRef;
import soot.jimple.Stmt;
import soot.jimple.ThisRef;
import soot.jimple.infoflow.AbstractInfoflow;
import soot.jimple.infoflow.BiDirICFGFactory;
import soot.jimple.infoflow.InfoflowResults;
import soot.jimple.infoflow.InfoflowResults.SinkInfo;
import soot.jimple.infoflow.InfoflowResults.SourceInfo;
import soot.jimple.infoflow.aliasing.FlowSensitiveAliasStrategy;
import soot.jimple.infoflow.aliasing.IAliasingStrategy;
import soot.jimple.infoflow.aliasing.PtsBasedAliasStrategy;
import soot.jimple.infoflow.config.IInfoflowConfig;
import soot.jimple.infoflow.data.AbstractionAtSink;
import soot.jimple.infoflow.data.AccessPath;
import soot.jimple.infoflow.data.pathBuilders.DefaultPathBuilderFactory;
import soot.jimple.infoflow.data.pathBuilders.IAbstractionPathBuilder;
import soot.jimple.infoflow.data.pathBuilders.IPathBuilderFactory;
import soot.jimple.infoflow.entryPointCreators.IEntryPointCreator;
import soot.jimple.infoflow.handlers.ResultsAvailableHandler;
import soot.jimple.infoflow.handlers.TaintPropagationHandler;
import soot.jimple.infoflow.ipc.DefaultIPCManager;
import soot.jimple.infoflow.ipc.IIPCManager;
import soot.jimple.infoflow.problems.BackwardsInfoflowProblem;
import soot.jimple.infoflow.problems.InfoflowProblem;
import soot.jimple.infoflow.solver.BackwardsInfoflowCFG;
import soot.jimple.infoflow.solver.IInfoflowCFG;
import soot.jimple.infoflow.solver.fastSolver.InfoflowSolver;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.jimple.infoflow.util.SootMethodRepresentationParser;
import soot.jimple.infoflow.util.SystemClassHandler;
import soot.jimple.internal.InvokeExprBox;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JCmpExpr;
import soot.jimple.internal.JGotoStmt;
import soot.jimple.internal.JIdentityStmt;
import soot.jimple.internal.JIfStmt;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JLookupSwitchStmt;
import soot.jimple.internal.JNeExpr;
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JReturnStmt;
import soot.jimple.internal.JSpecialInvokeExpr;
import soot.jimple.internal.JStaticInvokeExpr;
import soot.jimple.internal.JThrowStmt;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.internal.RValueBox;
import soot.jimple.spark.pag.PAG;
import soot.jimple.spark.solver.OnFlyCallGraph;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.options.Options;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.scalar.SimpleLiveLocals;
import soot.toolkits.scalar.SmartLocalDefs;
import soot.util.queue.QueueReader;
/**
 * main infoflow class which triggers the analysis and offers method to customize it.
 *
 */
public class MyInfoflow extends AbstractInfoflow {
	
    private final Logger logger = LoggerFactory.getLogger(getClass());
    
    private static int THRESHOLD = 60;
    
	private static int accessPathLength = 5;
	private static boolean useRecursiveAccessPaths = true;
	private static boolean pathAgnosticResults = true;
	
	private InfoflowResults results = null;
	private final IPathBuilderFactory pathBuilderFactory;

	private final String androidPath;
	private final boolean forceAndroidJar;
	private IInfoflowConfig sootConfig;
	
	private IIPCManager ipcManager = new DefaultIPCManager(new ArrayList<String>());
	
    private IInfoflowCFG iCfg;
    
    private Set<ResultsAvailableHandler> onResultsAvailable = new HashSet<ResultsAvailableHandler>();
    private Set<TaintPropagationHandler> taintPropagationHandlers = new HashSet<TaintPropagationHandler>();

	private String mGraph;
	private boolean thirdPartyAbortBroadcast = false;
	private boolean sendMsg = false;
	private boolean readAddress = false;
	private boolean readBody = false;
	private boolean fakePutSms = false;
	
	private List<Unit> src = new ArrayList<>();
	private List<Unit> snk = new ArrayList<>();

	private static boolean XX = false;
	
	private static Map<String, Map<String,String>> SIGNATURE_MAP = new HashMap<String, Map<String,String>>();
	static{
		SIGNATURE_MAP.put("java.lang.Thread", new HashMap<String,String>(){{put("void start()","void run()");}});
		SIGNATURE_MAP.put("android.os.AsyncTask", new HashMap<String,String>(){{put("android.os.AsyncTask execute(java.lang.Object[])","java.lang.Object doInBackground(java.lang.Object[])");}});
		SIGNATURE_MAP.put("android.os.AsyncTask", new HashMap<String,String>(){{put("android.os.AsyncTask execute(java.lang.Object[])","void onPostExecute(java.lang.Object)");}});
		SIGNATURE_MAP.put("android.os.Handler", new HashMap<String,String>(){{put("boolean sendMessage(android.os.Message)","void handleMessage(android.os.Message)");}});
//		SIGNATURE_MAP.put("android.os.Handler",void onReceive(android.content.Context,android.content.Intent)
		//		SIGNATURE_MAP.put(key, value);
	}

	/**
	 * Creates a new instance of the InfoFlow class for analyzing plain Java code without any references to APKs or the Android SDK.
	 */
	public MyInfoflow() {
		this.androidPath = "";
		this.forceAndroidJar = false;
		this.pathBuilderFactory = new DefaultPathBuilderFactory();
	}

	/**
	 * Creates a new instance of the Infoflow class for analyzing Android APK files.
	 * @param androidPath If forceAndroidJar is false, this is the base directory
	 * of the platform files in the Android SDK. If forceAndroidJar is true, this
	 * is the full path of a single android.jar file.
	 * @param forceAndroidJar True if a single platform JAR file shall be forced,
	 * false if Soot shall pick the appropriate platform version 
	 */
	public MyInfoflow(String androidPath, boolean forceAndroidJar) {
		super();
		this.androidPath = androidPath;
		this.forceAndroidJar = forceAndroidJar;
		this.pathBuilderFactory = new DefaultPathBuilderFactory();
	}

	/**
	 * Creates a new instance of the Infoflow class for analyzing Android APK files.
	 * @param androidPath If forceAndroidJar is false, this is the base directory
	 * of the platform files in the Android SDK. If forceAndroidJar is true, this
	 * is the full path of a single android.jar file.
	 * @param forceAndroidJar True if a single platform JAR file shall be forced,
	 * false if Soot shall pick the appropriate platform version
	 * @param icfgFactory The interprocedural CFG to be used by the InfoFlowProblem
	 * @param pathBuilderFactory The factory class for constructing a path builder
	 * algorithm 
	 */
	public MyInfoflow(String androidPath, boolean forceAndroidJar, BiDirICFGFactory icfgFactory,
			IPathBuilderFactory pathBuilderFactory) {
		super(icfgFactory);
		this.androidPath = androidPath;
		this.forceAndroidJar = forceAndroidJar;
		this.pathBuilderFactory = pathBuilderFactory;
	}
	
	public void setSootConfig(IInfoflowConfig config){
		sootConfig = config;
	}
	
	/**
	 * Initializes Soot.
	 * @param appPath The application path containing the analysis client
	 * @param libPath The Soot classpath containing the libraries
	 * @param classes The set of classes that shall be checked for data flow
	 * analysis seeds. All sources in these classes are used as seeds.
	 * @param sourcesSinks The manager object for identifying sources and sinks
	 */
	private void initializeSoot(String appPath, String libPath, Set<String> classes) {
		initializeSoot(appPath, libPath, classes,  "");
	}
	
	/**
	 * Initializes Soot.
	 * @param appPath The application path containing the analysis client
	 * @param libPath The Soot classpath containing the libraries
	 * @param classes The set of classes that shall be checked for data flow
	 * analysis seeds. All sources in these classes are used as seeds. If a
	 * non-empty extra seed is given, this one is used too.
	 */
	private void initializeSoot(String appPath, String libPath, Set<String> classes,
			String extraSeed) {
		// reset Soot:
		logger.info("Resetting Soot...");
		soot.G.reset();
				
		Options.v().set_no_bodies_for_excluded(true);
		Options.v().set_allow_phantom_refs(true);
		if (logger.isDebugEnabled())
			Options.v().set_output_format(Options.output_format_jimple);
		else
			Options.v().set_output_format(Options.output_format_none);
		
		// We only need to distinguish between application and library classes
		// if we use the OnTheFly ICFG
		if (callgraphAlgorithm == CallgraphAlgorithm.OnDemand) {
			Options.v().set_soot_classpath(libPath);
			if (appPath != null) {
				List<String> processDirs = new LinkedList<String>();
				for (String ap : appPath.split(File.pathSeparator))
					processDirs.add(ap);
				Options.v().set_process_dir(processDirs);
			}
		}
		else
			Options.v().set_soot_classpath(appPath + File.pathSeparator + libPath);
		
		// Configure the callgraph algorithm
		switch (callgraphAlgorithm) {
			case AutomaticSelection:
				// If we analyze a distinct entry point which is not static,
				// SPARK fails due to the missing allocation site and we fall
				// back to CHA.
				if (extraSeed == null || extraSeed.isEmpty()) {
					Options.v().setPhaseOption("cg.spark", "on");
					Options.v().setPhaseOption("cg.spark", "string-constants:true");
				}
				else
					Options.v().setPhaseOption("cg.cha", "on");
				break;
			case CHA:
				Options.v().setPhaseOption("cg.cha", "on");
				break;
			case RTA:
				Options.v().setPhaseOption("cg.spark", "on");
				Options.v().setPhaseOption("cg.spark", "rta:true");
				Options.v().setPhaseOption("cg.spark", "string-constants:true");
				break;
			case VTA:
				Options.v().setPhaseOption("cg.spark", "on");
				Options.v().setPhaseOption("cg.spark", "vta:true");
				Options.v().setPhaseOption("cg.spark", "string-constants:true");
				break;
			case SPARK:
				Options.v().setPhaseOption("cg.spark", "on");
				Options.v().setPhaseOption("cg.spark", "string-constants:true");
				break;
			case OnDemand:
				// nothing to set here
				break;
			default:
				throw new RuntimeException("Invalid callgraph algorithm");
		}
		
		// Specify additional options required for the callgraph
		if (callgraphAlgorithm != CallgraphAlgorithm.OnDemand) {
			Options.v().set_whole_program(true);
			Options.v().setPhaseOption("cg", "trim-clinit:false");
		}

		// do not merge variables (causes problems with PointsToSets)
		Options.v().setPhaseOption("jb.ulp", "off");
		
		if (!this.androidPath.isEmpty()) {
			Options.v().set_src_prec(Options.src_prec_apk);
			if (this.forceAndroidJar)
				soot.options.Options.v().set_force_android_jar(this.androidPath);
			else
				soot.options.Options.v().set_android_jars(this.androidPath);
		} else
			Options.v().set_src_prec(Options.src_prec_java);
		
		//at the end of setting: load user settings:
		if (sootConfig != null)
			sootConfig.setSootOptions(Options.v());
		
		// load all entryPoint classes with their bodies
		Scene.v().loadNecessaryClasses();
		logger.info("Basic class loading done.");
		boolean hasClasses = false;
		for (String className : classes) {
			SootClass c = Scene.v().forceResolve(className, SootClass.BODIES);
			if (c != null){
				c.setApplicationClass();
				if(!c.isPhantomClass() && !c.isPhantom())
					hasClasses = true;
			}
		}
		if (!hasClasses) {
			logger.error("Only phantom classes loaded, skipping analysis...");
			return;
		}
	}

	@Override
	public void computeInfoflow(String appPath, String libPath,
			IEntryPointCreator entryPointCreator,
			ISourceSinkManager sourcesSinks) {
		if (sourcesSinks == null) {
			logger.error("Sources are empty!");
			return;
		}
		
		Set<String> requiredClasses = SootMethodRepresentationParser.v().parseClassNames
				(entryPointCreator.getRequiredClasses(), false).keySet();
		
		initializeSoot(appPath, libPath, requiredClasses);

		// entryPoints are the entryPoints required by Soot to calculate Graph - if there is no main method,
		// we have to create a new main method and use it as entryPoint and store our real entryPoints
		Scene.v().setEntryPoints(Collections.singletonList(entryPointCreator.createDummyMain()));
		ipcManager.updateJimpleForICC();
		
		// We explicitly select the packs we want to run for performance reasons
		if (callgraphAlgorithm != CallgraphAlgorithm.OnDemand) {
	        PackManager.v().getPack("wjpp").apply();
	        PackManager.v().getPack("cg").apply();
		}
        runAnalysis(sourcesSinks, null);
		if (logger.isDebugEnabled())
			PackManager.v().writeOutput();
	}


	@Override
	public void computeInfoflow(String appPath, String libPath, String entryPoint,
			ISourceSinkManager sourcesSinks) {
		if (sourcesSinks == null) {
			logger.error("Sources are empty!");
			return;
		}

		initializeSoot(appPath, libPath,
				SootMethodRepresentationParser.v().parseClassNames
					(Collections.singletonList(entryPoint), false).keySet(), entryPoint);

		if (!Scene.v().containsMethod(entryPoint)){
			logger.error("Entry point not found: " + entryPoint);
			return;
		}
		SootMethod ep = Scene.v().getMethod(entryPoint);
		if (ep.isConcrete())
			ep.retrieveActiveBody();
		else {
			logger.debug("Skipping non-concrete method " + ep);
			return;
		}
		Scene.v().setEntryPoints(Collections.singletonList(ep));
		Options.v().set_main_class(ep.getDeclaringClass().getName());
		
		// Compute the additional seeds if they are specified
		Set<String> seeds = Collections.emptySet();
		if (entryPoint != null && !entryPoint.isEmpty())
			seeds = Collections.singleton(entryPoint);

		ipcManager.updateJimpleForICC();
		// We explicitly select the packs we want to run for performance reasons
		if (callgraphAlgorithm != CallgraphAlgorithm.OnDemand) {
	        PackManager.v().getPack("wjpp").apply();
	        PackManager.v().getPack("cg").apply();
		}
        runAnalysis(sourcesSinks, seeds);
		if (logger.isDebugEnabled())
			PackManager.v().writeOutput();
	}
	
	/**
	 * 找出语句中的右边值
	 * @param unit
	 * @return
	 */
	private Value findRightValueInUnit(Unit unit) {
		
		Value rightValue = null;
		if(unit instanceof JAssignStmt) {
			
			JAssignStmt localassignStmt = (JAssignStmt) unit;
			ValueBox localrightvb = localassignStmt.rightBox;
			rightValue = localrightvb.getValue();
		}
		else if(unit instanceof JIdentityStmt) {
			JIdentityStmt localidentityStmt = (JIdentityStmt) unit;
			ValueBox localrightvb = localidentityStmt.rightBox;
			rightValue = localrightvb.getValue();
		}
		else {	//变量的定义语句似乎只有JAssignStmt和JIdentityStmt，应该不包括其它类型的语句
			System.out.println("Unbelievable Unit Type: " + unit);
		}
		
		return rightValue;
	}
	
	/**
	 * 分析类成员变量sfr在方法 method中的赋值情况
	 * @param cg
	 * @param method
	 * @param sfr
	 */
	private void analyzeJInstanceFieldRef(CallGraph cg, SootMethod method, SootFieldRef sfr) {
		
		long begin = System.currentTimeMillis();
		
		MyScene myscene = MyScene.v();
		Body mbody = method.getActiveBody();
		
		SootClass sc = method.getDeclaringClass();
		if(sc.getName().startsWith("java.") || sc.getName().startsWith("android.")) {
//			System.out.println("no need to analyze system lib Class!");
			return ;
		}
		
		List<ValueBox> vbList = mbody.getDefBoxes();
		
		for(ValueBox defvb : vbList) {
			Value v = defvb.getValue();
			if(!(v instanceof JInstanceFieldRef)) {	//说明这个变量定义不是类成员变量的定义
				continue;
			}
			
			if(!((JInstanceFieldRef) v).getFieldRef().equals(sfr)) {	//说明这个类成员变量不是这次要分析的成员变量
				continue;
			}
			
			//对类成员变量赋值
			Stmt stmt = findVbInUnits(mbody, defvb);
			if(!(stmt instanceof JAssignStmt)) {	//忽略非赋值语句
				continue;
			}
			
			JAssignStmt assignStmt = (JAssignStmt) stmt;
			ValueBox rightvb = assignStmt.rightBox;
			Value rightValue = rightvb.getValue();
			
			List<Unit> ulist = new ArrayList<Unit>();
			Unit searchStmt = assignStmt;
			while(!(rightValue instanceof JNewExpr)) {
				if(rightValue instanceof JimpleLocal) {	//方法内局部变量赋值给类成员变量，这样的变量定义要从方法内找
					
					ExceptionalUnitGraph graph = new ExceptionalUnitGraph(method.retrieveActiveBody());
					SmartLocalDefs smd = new SmartLocalDefs(graph, new SimpleLiveLocals(graph));
					List<Unit> unitList = smd.getDefsOfAt((JimpleLocal)rightValue, searchStmt);
					
					ulist.addAll(unitList);	//把这个类局部变量的定义语句放到待分析列表中
				}
				else if(rightValue instanceof ParameterRef) {		//方法参数赋值给类成员变量，这样的变量定义要从函数调用中去找
					//变量引用是方法参数，获取上次的分析语句调用
					Iterator<Edge> eit = cg.edgesInto(method);	//找到这个方法的调用点，然后依次分析
					while(eit.hasNext()) {
						Edge edge = eit.next();
						MethodOrMethodContext srcmomc = edge.getSrc();
						analysisSootFieldRefInMethod(sfr,  (ParameterRef) rightValue, srcmomc, edge.srcUnit(), cg, 0);
					}
					
					rightValue = null;
				}
				else if(rightValue instanceof JInstanceFieldRef) {		//其它类成员变量赋值给类成员变量，将这两个类成员变量关联起来
					//如果从类成员变量中取值，则将两个类成员变量关联
					SootFieldRef ref = ((JInstanceFieldRef) rightValue).getFieldRef();
					myscene.addIdentityFieldRef(ref, sfr);
					
					rightValue = null;
				}
				else {
					//遇到没有预料到的变量类型
					System.out.println("enconutered illegal value: " + rightValue);
					rightValue = null;
				}
				
				if(ulist.size() == 0) {
					break;
				}
				
				while(ulist.size() > 0)
				{
					Unit unit = ulist.remove(0);
					searchStmt = unit;
					rightValue = findRightValueInUnit(unit);
					if(rightValue != null) {
						break;
					}
				}
				
				if(rightValue == null) {
					break;
				}
			}
			
			if(rightValue instanceof JNewExpr) {	//找到New语句，这是变量的初始化点
				JNewExpr newexpr = (JNewExpr) rightValue;
				SootClass tgtsc = newexpr.getBaseType().getSootClass();
				myscene.addFieldImplSootClass(sfr, tgtsc);
			}
		}
		
		System.out.println("analyze SootFieldRef：" + sfr + " cost time: " + (System.currentTimeMillis() - begin) / 1000);
	}

	
	private void runAnalysis(final ISourceSinkManager sourcesSinks, final Set<String> additionalSeeds) {
		// Run the preprocessors
        for (Transform tr : preProcessors)
            tr.apply();
        
		
        /*  */
//        Scene.v().addBasicClass("javax.net.ssl.HttpsURLConnection",0);
        CallGraph cg = Scene.v().getCallGraph();
        
//        analyzeSootFieldInstance(cg); 
//        analyzeIndirectCall(cg);

        
//        if(analyzeExistSmsCheat(cg)){
//        	return;
//        };
        
//        AbstractSootFeature.SOOT_INITIALIZED=true;
//        Set<AndroidMethod> toFindAsyncMethods = new HashSet<>();
//        Iterator<MethodOrMethodContext> methodIterator = cg.sourceMethods();
//		while (methodIterator.hasNext()) {
//			AndroidMethod e = new AndroidMethod(methodIterator.next().method());
//			toFindAsyncMethods.add(e);
//		}
//		Map<AndroidMethod, IFeature> sensitivityMethod;
//		try {
//			sensitivityMethod = new MySootAnalyzer(androidPath, "d:/susi.out", toFindAsyncMethods).run();
//		} catch (IOException e) {
//			e.printStackTrace();
//		}
        
        
//        GenerateVisualGraph gvg = new GenerateVisualGraph();
//        gvg.init(cg,getmGraph());
        
        PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
        if(pta instanceof PAG) {
        	PAG pag = (PAG) pta;
        	OnFlyCallGraph ofcg = pag.getOnFlyCallGraph();
        	ReachableMethods rm = ofcg.reachableMethods();
        	
        	
        	//first add Edges to CallGraph(cg), then call ofcg.build();
        	
//        	cg.addEdge(e);
        	ofcg.build();
        }
        
//        GenerateVisualGraph gvg = new GenerateVisualGraph();
//        gvg.init(cg,getmGraph());
        
        System.out.println("begin old analysis ... ");
        /* */
        
        oldrunAnalysis(sourcesSinks, additionalSeeds);
	}

	private boolean analyzeExistSmsCheat(CallGraph cg) {
		
		
		List<MethodOrMethodContext> methods = new ArrayList<MethodOrMethodContext>();
		Iterator<MethodOrMethodContext> iterator = cg.sourceMethods();
		
		while (iterator.hasNext()) {
			MethodOrMethodContext method = iterator.next();
//			void android.content.BroadcastReceiver.abortBroadcast()
//			if(method.method().getSubSignature().indexOf("void abortBroadcast()")>-1){
//				thirdPartyAbortBroadcast = true;//拦截广播
//			}
			methods.add(method);
		}
		
		
        for (MethodOrMethodContext method:methods) {
			List<SootClass> realClassHierarchy = new ArrayList<SootClass>();
			SootClass superClass = method.method().getDeclaringClass();
			while(superClass!=null){
				realClassHierarchy.add(superClass);
				if(superClass.hasSuperclass()){
					superClass = superClass.getSuperclass();
				}else{
					superClass=null;
				}
			}
			
			int i=0;
			Value relativeLeftOp=null;//只分析LOCAL的
			for(UnitBox ub:method.method().getActiveBody().getAllUnitBoxes()){
//				ContentResolver android.content.ContextWrapper.getContentResolver()
				Unit unit = ub.getUnit();
				if(unit instanceof JAssignStmt){
					JAssignStmt jAssignStmt = (JAssignStmt)unit;
					Value leftOp = jAssignStmt.getLeftOp();
					Value rightOp = jAssignStmt.getRightOp();
					handleAnalyzeResult(relativeLeftOp,leftOp, rightOp);
				}else if(unit instanceof JReturnStmt){
					System.out.println("JReturnStmt:\t\t"+unit);
				}else if(unit instanceof JIdentityStmt){
					System.out.println("JIdentityStmt:\t\t"+unit);
				}else if(unit instanceof JThrowStmt){
					System.out.println("JThrowStmt:\t\t"+unit);
				}else if(unit instanceof JInvokeStmt){
					JInvokeStmt jInvokeStmt = (JInvokeStmt)unit;
					handleAnalyzeResult(null,null,jInvokeStmt.getInvokeExpr());
				}else if(unit instanceof JIfStmt){
					JIfStmt jIfStmt = (JIfStmt)unit;
					Value conditionBoxValue = jIfStmt.getConditionBox().getValue();
					if(conditionBoxValue instanceof JCmpExpr){
						JCmpExpr jCmpExpr = (JCmpExpr)conditionBoxValue;
						Value op1 = jCmpExpr.getOp1();
						Value op2 = jCmpExpr.getOp2();
						if(relativeLeftOp!=null&&(relativeLeftOp.toString().equals(op1.toString())||relativeLeftOp.toString().equals(op2.toString()))){
							System.out.println("Compare address or body");
						}
					}
				}else if(unit instanceof JLookupSwitchStmt){
					System.out.println("JLookupSwitchStmt:\t\t"+unit);
				}else if(unit instanceof JGotoStmt){
					System.out.println("JGotoStmt:\t\t"+unit);
				}else{
					System.out.println("ELSE:\t\t"+unit);
				}
				i++;
				
			}
			for(ValueBox vb :method.method().getActiveBody().getUseAndDefBoxes()){
				Value val =vb.getValue();
				if(val instanceof JStaticInvokeExpr){
					JStaticInvokeExpr involkExpr = (JStaticInvokeExpr)val;
					involkExpr.getMethodRef().getSubSignature().equals("android.telephony.SmsMessage createFromPdu(byte[])");//读短信数据库
				}
				if(val instanceof JVirtualInvokeExpr){
					JVirtualInvokeExpr involkExpr = (JVirtualInvokeExpr)val;
					if(involkExpr.getMethodRef().getSubSignature().toString().equals("void abortBroadcast()")){
						System.out.println("APK abort broadcast");
					}//拦截短信事件
					if(involkExpr.getMethodRef().getSubSignature().toString().equals("void sendTextMessage(java.lang.String,java.lang.String,java.lang.String,android.app.PendingIntent,android.app.PendingIntent)")){
						System.out.println("APK send message");
					}//发短信
					if(involkExpr.getMethodRef().getSubSignature().toString().equals("java.lang.String getDisplayOriginatingAddress()")){
						System.out.println("APK read message address");
					}//读了源短信地址
					if(involkExpr.getMethodRef().getSubSignature().toString().equals("java.lang.String getDisplayMessageBody()")){
						System.out.println("APK read message body");
					}//读了源短信内容
					if((involkExpr.getMethodRef().declaringClass().getName().equals("android.content.ContentValues")&&involkExpr.getMethodRef().getSubSignature().toString().equals("void put(java.lang.String,java.lang.String)"))){
						System.out.println("APK modify local message");
					}//修改了短信内容
				}
			}
		}
        if(thirdPartyAbortBroadcast){
			System.out.println("APK abort broadcast");
		}
		if(sendMsg){
			System.out.println("APK send message");
		}
		if(readAddress){
			System.out.println("APK read message address");
		}
		if(readBody){
			System.out.println("APK read message body");
		}
		if(fakePutSms){
			System.out.println("APK modify local message");
		}
//		if(thirdPartyAbortBroadcast&&readAddress&&readBody&&(fakePutSms||redirectMsg)){
//			System.out.println("Found type 1 by cg");
//			return true;
//		}else{
//			return false;
//		}
		return true;
	}

	private void handleAnalyzeResult(Value relativeLeftOp,Value leftOp, Value rightOp) {
		int ret = analyzeOp(rightOp);
		switch(ret){
		case 1:
			thirdPartyAbortBroadcast=true;
			break;
		case 2:
			sendMsg=true;
			break;
		case 3:
			readAddress=true;
			relativeLeftOp = leftOp;
			break;
		case 4:
			readBody=true;
			relativeLeftOp = leftOp;
			break;
		case 5:
			fakePutSms=true;
			break;
		default:
			break;
		}
	}
	
	private int analyzeOp(Value Op) {
		if(Op instanceof JVirtualInvokeExpr){
			JVirtualInvokeExpr involkExpr = (JVirtualInvokeExpr)Op;
			if(involkExpr.getMethodRef().getSubSignature().toString().equals("void abortBroadcast()")){
				return 1;
			}//拦截短信事件
			if(involkExpr.getMethodRef().getSubSignature().toString().equals("void sendTextMessage(java.lang.String,java.lang.String,java.lang.String,android.app.PendingIntent,android.app.PendingIntent)")){
				return 2;
			}//发短信
			if(involkExpr.getMethodRef().getSubSignature().toString().equals("java.lang.String getDisplayOriginatingAddress()")){
				return 3;
			}//读了源短信地址
			if(involkExpr.getMethodRef().getSubSignature().toString().equals("java.lang.String getDisplayMessageBody()")){
				return 4;
			}//读了源短信内容
			if((involkExpr.getMethodRef().declaringClass().getName().equals("android.content.ContentValues")&&involkExpr.getMethodRef().getSubSignature().toString().equals("void put(java.lang.String,java.lang.String)"))){
				return 5;
			}//修改了短信内容
			return 0;
		}else{
			return 0;
		}

	}

	private void oldrunAnalysis(final ISourceSinkManager sourcesSinks, final Set<String> additionalSeeds) {
		// Run the preprocessors
		

        if (callgraphAlgorithm != CallgraphAlgorithm.OnDemand)
        	logger.info("Callgraph has {} edges", Scene.v().getCallGraph().size());
        iCfg = icfgFactory.buildBiDirICFG(callgraphAlgorithm);
        
        int numThreads = Runtime.getRuntime().availableProcessors();
		CountingThreadPoolExecutor executor = createExecutor(numThreads);
		
		BackwardsInfoflowProblem backProblem;
		InfoflowSolver backSolver;
		final IAliasingStrategy aliasingStrategy;
		switch (aliasingAlgorithm) {
			case FlowSensitive:
				backProblem = new BackwardsInfoflowProblem(new BackwardsInfoflowCFG(iCfg), sourcesSinks);
				// need to set this before creating the zero abstraction
				backProblem.setFlowSensitiveAliasing(flowSensitiveAliasing);
				
				backSolver = new InfoflowSolver(backProblem, executor);
				backSolver.setJumpPredecessors(!computeResultPaths);
//				backSolver.setEnableMergePointChecking(true);
				
				aliasingStrategy = new FlowSensitiveAliasStrategy(iCfg, backSolver);
				break;
			case PtsBased:
				backProblem = null;
				backSolver = null;
				aliasingStrategy = new PtsBasedAliasStrategy(iCfg);
				break;
			default:
				throw new RuntimeException("Unsupported aliasing algorithm");
		}
		
		InfoflowProblem forwardProblem  = new InfoflowProblem(iCfg, sourcesSinks,
				aliasingStrategy);
		// need to set this before creating the zero abstraction
		forwardProblem.setFlowSensitiveAliasing(flowSensitiveAliasing);
		if (backProblem != null)
			forwardProblem.setZeroValue(backProblem.createZeroValue());
		
		// Set the options
		InfoflowSolver forwardSolver = new InfoflowSolver(forwardProblem, executor);
		aliasingStrategy.setForwardSolver(forwardSolver);
		forwardSolver.setJumpPredecessors(!computeResultPaths);
//		forwardSolver.setEnableMergePointChecking(true);
		
		forwardProblem.setInspectSources(inspectSources);
		forwardProblem.setInspectSinks(inspectSinks);
		forwardProblem.setEnableImplicitFlows(enableImplicitFlows);
		forwardProblem.setEnableStaticFieldTracking(enableStaticFields);
		forwardProblem.setEnableExceptionTracking(enableExceptions);
		for (TaintPropagationHandler tp : taintPropagationHandlers)
			forwardProblem.addTaintPropagationHandler(tp);
		forwardProblem.setTaintWrapper(taintWrapper);
		forwardProblem.setStopAfterFirstFlow(stopAfterFirstFlow);
		forwardProblem.setIgnoreFlowsInSystemPackages(ignoreFlowsInSystemPackages);
		
		if (backProblem != null) {
			backProblem.setForwardSolver((InfoflowSolver) forwardSolver);
			backProblem.setTaintWrapper(taintWrapper);
			backProblem.setEnableStaticFieldTracking(enableStaticFields);
			backProblem.setEnableExceptionTracking(enableExceptions);
			for (TaintPropagationHandler tp : taintPropagationHandlers)
				backProblem.addTaintPropagationHandler(tp);
			backProblem.setTaintWrapper(taintWrapper);
			backProblem.setActivationUnitsToCallSites(forwardProblem);
			backProblem.setIgnoreFlowsInSystemPackages(ignoreFlowsInSystemPackages);
			backProblem.setInspectSources(inspectSources);
			backProblem.setInspectSinks(inspectSinks);
		}
		
		if (!enableStaticFields)
			logger.warn("Static field tracking is disabled, results may be incomplete");
		if (!flowSensitiveAliasing || !aliasingStrategy.isFlowSensitive())
			logger.warn("Using flow-insensitive alias tracking, results may be imprecise");

		// We have to look through the complete program to find sources
		// which are then taken as seeds.
		int sinkCount = 0;
        logger.info("Looking for sources and sinks...");
                
        for (SootMethod sm : getMethodsForSeeds(iCfg)) {
//        	if(sm.getDeclaringClass().getName().startsWith("com.example")) 
//        		if(sm.getDeclaringClass().getName().equals("com.example.test4.MainActivity")) 
        	{
        		sinkCount += scanMethodForSourcesSinks(sourcesSinks, forwardProblem, sm);
        	}
        }
        
		// We optionally also allow additional seeds to be specified
		if (additionalSeeds != null)
			for (String meth : additionalSeeds) {
				SootMethod m = Scene.v().getMethod(meth);
				if (!m.hasActiveBody()) {
					logger.warn("Seed method {} has no active body", m);
					continue;
				}
				forwardProblem.addInitialSeeds(m.getActiveBody().getUnits().getFirst(),
						Collections.singleton(forwardProblem.zeroValue()));
			}
		
		if (!forwardProblem.hasInitialSeeds() || sinkCount == 0){
			logger.error("No sources or sinks found, aborting analysis");
			return;
		}

		logger.info("Source lookup done, found {} sources and {} sinks.", forwardProblem.getInitialSeeds().size(),
				sinkCount);
		
		if(XX ){
		forwardSolver.solve();
		
		// Not really nice, but sometimes Heros returns before all
		// executor tasks are actually done. This way, we give it a
		// chance to terminate gracefully before moving on.
		int terminateTries = 0;
		while (terminateTries < 10) {
			if (executor.getActiveCount() != 0 || !executor.isTerminated()) {
				terminateTries++;
				try {
					Thread.sleep(500);
				}
				catch (InterruptedException e) {
					logger.error("Could not wait for executor termination", e);
				}
			}
			else
				break;
		}
		if (executor.getActiveCount() != 0 || !executor.isTerminated())
			logger.error("Executor did not terminate gracefully");

		// Print taint wrapper statistics
		if (taintWrapper != null) {
			logger.info("Taint wrapper hits: " + taintWrapper.getWrapperHits());
			logger.info("Taint wrapper misses: " + taintWrapper.getWrapperMisses());
		}
		
		Set<AbstractionAtSink> res = forwardProblem.getResults();

		logger.info("IFDS problem with {} forward and {} backward edges solved, "
				+ "processing {} results...", forwardSolver.propagationCount,
				backSolver == null ? 0 : backSolver.propagationCount,
				res == null ? 0 : res.size());
		
		// Force a cleanup. Everything we need is reachable through the
		// results set, the other abstractions can be killed now.
		forwardSolver.cleanup();
		if (backSolver != null) {
			backSolver.cleanup();
			backSolver = null;
			backProblem = null;
		}
		forwardSolver = null;
		forwardProblem = null;
		AccessPath.clearBaseRegister();
		Runtime.getRuntime().gc();
		
		computeTaintPaths(res);
		
		if (results.getResults().isEmpty())
			logger.warn("No results found.");
		else for (Entry<SinkInfo, Set<SourceInfo>> entry : results.getResults().entrySet()) {
			logger.info("The sink {} in method {} was called with values from the following sources:",
                    entry.getKey(), iCfg.getMethodOf(entry.getKey().getContext()).getSignature() );
			for (SourceInfo source : entry.getValue()) {
				logger.info("- {} in method {}",source, iCfg.getMethodOf(source.getContext()).getSignature());
				if (source.getPath() != null && !source.getPath().isEmpty()) {
					logger.info("\ton Path: ");
					for (Unit p : source.getPath()) {
						logger.info("\t -> " + iCfg.getMethodOf(p));
						logger.info("\t\t -> " + p);
					}
				}
			}
		}
		
		for (ResultsAvailableHandler handler : onResultsAvailable)
			handler.onResultsAvailable(iCfg, results);
		}
	}
	
	/**
	 * 分析函数的间接调用，并将间接调用以Edge的方式体现在CallGraph中
	 * @param cg
	 */
	private void analyzeIndirectCall(CallGraph cg) {
		QueueReader<MethodOrMethodContext> qr = Scene.v().getReachableMethods().listener();
  		while(qr.hasNext()) {	//依次搜索所有的方法
  			MethodOrMethodContext momc = qr.next();
  			SootMethod m = momc.method();
  			
//  			if(m.getSubSignature().equals("void onCreate(android.os.Bundle)")) {
//  				System.out.println("");
//  			}
  			
  			SootClass sc = m.getDeclaringClass();
  			
  			if(sc.getName().startsWith("java.") || sc.getName().startsWith("android.")) {
//  				System.out.println("no need to analyze system lib Class!");
  				continue ;
  			}
  			
  			if(m.hasActiveBody()) {//如果尚未有函数体，则先获得函数体
  				try {
  					m.retrieveActiveBody();
  				}
  				catch(Throwable t) {
  					System.out.println(t);
  					continue;
  				}
  			}
  			
  			if(!m.hasActiveBody()) {
  				continue;
  			}
  			
  			Body body = m.getActiveBody();
  			
  			Iterator<Unit> uit = body.getUnits().iterator();
  			while(uit.hasNext()) {	//依次遍历所有定义和使用的box
  				
  				Unit unit = uit.next();
  				if(!(unit instanceof JInvokeStmt)) {
  					//对于非函数调用语句，不必分析
  					continue;
  				}
  				
  				//要分析出两个内容：1、这个函数是哪个类（对象）调用的；2、这个调用方法是哪个类的方法
  				JInvokeStmt invoke = (JInvokeStmt) unit;
  				InvokeExpr expr = invoke.getInvokeExpr();	//得到调用函数表达式
  				SootMethod baseMethod = expr.getMethod();	//得到函数
  				
  				ValueBox vb = getBaseBox(expr);
  				if(vb != null) {
  					
  					long begin = System.currentTimeMillis();
					List<SootClass> sclist = getSootClassListForValueBox(vb.getValue(), unit, m, cg);
					System.out.println("getSootClassListForValueBox cost time: " + (System.currentTimeMillis() - begin) / 1000 + "; " + vb.getValue());
					Set<SootClass> scset = new HashSet<SootClass>();
					
					for(SootClass invokeClass : sclist) {
						if(scset.add(invokeClass)) {
							SootMethod tgt = findTargetMethod(invokeClass, baseMethod);
							if(tgt!=null)	{
								soot.jimple.toolkits.callgraph.Edge e=new soot.jimple.toolkits.callgraph.Edge(m, invoke, tgt);
								cg.addEdge(e);
							}
						}
					}
  				}
  				else {
  					//FIXME vb is null, this is static method call
  					System.out.println("you must process static method call!");
  				}
  				
  				System.out.println("");
  			}
  		}
	}
	
	/**
	 * 获取此调用语句的调用者Box
	 * @param expr
	 * @return
	 */
	private ValueBox getBaseBox(InvokeExpr expr) {
		ValueBox vb = null;
		if(expr instanceof JVirtualInvokeExpr) {
			vb = ((JVirtualInvokeExpr) expr).getBaseBox();
		}
		else if(expr instanceof JSpecialInvokeExpr) {
			vb = ((JSpecialInvokeExpr) expr).getBaseBox();
		}
		else if(expr instanceof JStaticInvokeExpr) {
			//for static call, there is no basebox
		}
		
		return vb;
	}
	
	private List<Unit> getPreUnitList(List<Unit> ulist, Unit unit, SootMethod method) {
		Iterator<Unit> uit = method.getActiveBody().getUnits().iterator();
		List<Unit> list = new ArrayList<>();
		while(uit.hasNext()) {
			Unit u = uit.next();
			if(u.equals(unit)) {
				break;
			}
			
			if(ulist.contains(u)) {
				list.add(u);
			}
		}
		
		return list;
	}
	
	private boolean isasyncClassRelated(SootClass sc) {
		Iterator<String> sit = SIGNATURE_MAP.keySet().iterator();
		List<String> list = new ArrayList<String>();
		while(sit.hasNext()) {
			list.add(sit.next());
		}
		
		List<SootClass> sclist = new ArrayList<>();
		sclist.add(sc);
		
		while(sclist.size() > 0) {
			sc = sclist.remove(0);
			if(sc.hasSuperclass()) {
				sclist.add(sc.getSuperclass());
			}
			
			Iterator<SootClass> scit = sc.getInterfaces().iterator();
			while(scit.hasNext()) {
				SootClass interfaceSc = scit.next();
				sclist.add(interfaceSc);
			}
			
			String classname = sc.getName();
			if(list.contains(classname)) {
				return true;
			}
		}
		
		return false;
	}
	
	/**
	 * 获取unit语句中出现的value变量的实际定义类型
	 * @param value	重点变量
	 * @param unit	出现变量value的unit语句
	 * @param method unit语句所在的方法
	 * @param cg
	 * @return
	 */
	private List<SootClass> getSootClassListForValueBox(Value value, Unit unit, SootMethod method, CallGraph cg) {
		
		MyScene myscene = MyScene.v();
		List<SootClass> sclist = new ArrayList<SootClass>();
		
		if(value instanceof JimpleLocal) {
			JimpleLocal local = (JimpleLocal) value;
			
			SootClass sc = ((RefType)local.getType()).getSootClass();
			if(!isasyncClassRelated(sc)) {
				System.out.println("concern indirect call, ignore SootClass: " + sc);
				return sclist;
			}
			
			ExceptionalUnitGraph graph = new ExceptionalUnitGraph(method.retrieveActiveBody());
			SmartLocalDefs smd = new SmartLocalDefs(graph, new SimpleLiveLocals(graph));
			List<Unit> uList = smd.getDefsOfAt(local, unit);
			
			uList = getPreUnitList(uList, unit, method);
			//FIXME 只处理最近一次出现的局部变量定义语句，因此，把for循环去掉，只处理uList中的最后一个语句
			
			Unit u = uList.size() == 0 ? null : uList.get(uList.size() - 1);
			if(u == null) {
				return sclist;
			}
//			for(Unit u : uList) 
			{
				Value v = findRightValueInUnit(u);
				if(v instanceof JimpleLocal) {
					sclist.addAll(getSootClassListForValueBox(v, u, method, cg));
				}
				else if(v instanceof ParameterRef) {
					Iterator<Edge> eit = cg.edgesInto(method);	//找到这个方法的调用点，然后依次分析
					while(eit.hasNext()) {
						Edge edge = eit.next();
						MethodOrMethodContext srcmomc = edge.getSrc();
						sclist.addAll(analysisActualParaInMethod((ParameterRef) v, srcmomc, edge.srcUnit(), cg, 0, new ArrayList<MethodOrMethodContext>()));
					}
				}
				else if(v instanceof JInstanceFieldRef) {	
					SootFieldRef sfr = ((JInstanceFieldRef) v).getFieldRef();
					sclist.addAll(myscene.getInstanceImpl(sfr));
				}
				else if(v instanceof JNewExpr) {
					JNewExpr newexpr = (JNewExpr) v;
					SootClass tgtsc = newexpr.getBaseType().getSootClass();
					sclist.add(tgtsc);
				}
				else if(v instanceof ThisRef) {
					ThisRef tr = (ThisRef)v;
					if(tr.getType() instanceof RefType) {
						RefType reftype = (RefType) (tr.getType());
						SootClass tgtsc = reftype.getSootClass();
						sclist.add(tgtsc);
					}
				}
				else {
					//FIXME 还要考虑函数调用返回值
					System.out.println("unexpected def unit type!" + v);
				}
			}
		}
		else {
			System.out.println("value must be JimpleLocal");
		}
		
		return sclist;
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
			SootClass realInvokeClass = canFindSootClass(realClassHierarchy,key);
			if(realInvokeClass!=null){
				for(String fromMethod:SIGNATURE_MAP.get(key).keySet()){
					if(subSignature.equals(fromMethod)){
						String toMethod = SIGNATURE_MAP.get(key).get(fromMethod);
						tgt = realInvokeClass.getMethod(toMethod);
						System.err.println("find async call "+fromMethod);
					}
				}
			}
		}
		return tgt;
	}
	
	private SootClass canFindSootClass(List<SootClass> realClassHierarchy,
			String key) {
		for(SootClass sc:realClassHierarchy){
			if(sc.getName().equals(key)){
				return sc;
			}
		}
		return null;
	}
	
	/**
	 * 分析程序可达方法的类成员变量实例化情况，并将结果保存在MyScene中
	 * @param cg
	 */
	private void analyzeSootFieldInstance(CallGraph cg) {
		MyScene myscene = MyScene.v();
	      
        //added by lixun
  		QueueReader<MethodOrMethodContext> qr = Scene.v().getReachableMethods().listener();
  		while(qr.hasNext()) {	//依次搜索所有的方法
  			MethodOrMethodContext momc = qr.next();
  			SootMethod m = momc.method();
  			
  			SootClass sc = m.getDeclaringClass();
  			
  			if(sc.getName().startsWith("java.") || sc.getName().startsWith("android.")) {
//  				System.out.println("no need to analyze system lib Class!");
  				continue ;
  			}
  			
  			if(m.hasActiveBody()) {//如果尚未有函数体，则先获得函数体
  				try {
  					m.retrieveActiveBody();
  				}
  				catch(Throwable t) {
  					System.out.println(t);
  					continue;
  				}
  			}
  			
  			if(!m.hasActiveBody()) {
  				continue;
  			}
  			
  			Body body = m.getActiveBody();
  			
  			List<ValueBox> useAndDef = body.getUseAndDefBoxes();
  			for(ValueBox vb : useAndDef) {	//依次遍历所有定义和使用的box
  				if(!(vb instanceof RValueBox)) {
  					//如果此box不是右边使用的，则暂时不分析
  					continue;
  				}

  				RValueBox rvb = (RValueBox) vb;
  				Value value = rvb.getValue();
  				if(value instanceof JInstanceFieldRef) {//目前分析类成员变量
  					JInstanceFieldRef fieldRef = (JInstanceFieldRef) value;
  					SootFieldRef sfr = fieldRef.getFieldRef();
  					
  					if(!(myscene.addSootClass(sc) || myscene.addFieldSet(sfr))) {
  						//这个类成员变量已经添加过，不必重复添加
  						continue;
  					}
  						
  					myscene.addSootFieldRef(sc, sfr);
  					//搜索这个类的所有方法，找到这个类成员变量定义的地方，
  					
  					List<SootMethod> methodList = sc.getMethods();
  					for(SootMethod method : methodList) {
  						
  						if(!method.hasActiveBody()) {
  							try {
  			  					m.retrieveActiveBody();
  			  				}
  			  				catch(Throwable t) {
  			  					System.out.println(t);
  			  					continue;
  			  				}
  						}
  						
  						if(!method.hasActiveBody()) {
  							continue;
  						}
  						
  						analyzeJInstanceFieldRef(cg, method, sfr); //分析类成员变量sfr在方法 method中的赋值情况
  					}
  				}
  			}
  		}
  		
  		myscene.reorgnizeIdentityFieldRef();
  		System.out.println("Class member object analysis finished!");
	}
	
	/**
	 * 获取方法参数对象的实际类型
	 * @param pararef	方法参数
	 * @param srcmomc	方法
	 * @param unit	调用语句
	 * @param cg	
	 * @param level
	 * @param mlist 之前出现过的调用函数列表
	 * @return
	 */
	private List<SootClass> analysisActualParaInMethod(ParameterRef pararef, MethodOrMethodContext srcmomc, Unit unit, CallGraph cg, int level, List<MethodOrMethodContext> mlist) {
		
		if(level > THRESHOLD) {
			System.out.println("can not continue because of deep level: " + level);
			return new ArrayList<SootClass>();
		}
		
		SootClass sc = srcmomc.method().getDeclaringClass();
		if(sc.getName().startsWith("java.") || sc.getName().startsWith("android.")) {
//			System.out.println("no need to analyze system lib Class!");
			return new ArrayList<SootClass>();
		}
		
		List<SootClass> sclist = new ArrayList<SootClass>();
		MyScene myscene = MyScene.v();
		
		SootMethod method = srcmomc.method();
		
		if(!(unit instanceof JInvokeStmt)) { //必须是函数调用语句
			return sclist;
		}
		
		JInvokeStmt stmt = (JInvokeStmt) unit;
		InvokeExprBox exprBox = (InvokeExprBox) stmt.getInvokeExprBox();
		
		Value value = exprBox.getValue();
		assert value instanceof InvokeExpr;
//		if(!(value instanceof InvokeExpr)) {
//			return;
//		}
		
		Value rightValue = ((InvokeExpr) value).getArg(pararef.getIndex()); 
		
		Unit searchStmt = unit;
		List<Unit> ulist = new ArrayList<Unit>();
		
		while(!(rightValue instanceof JNewExpr)) {
			if(rightValue instanceof JimpleLocal) {	//方法内局部变量赋值给类成员变量，这样的变量定义要从方法内找
				
				ExceptionalUnitGraph graph = new ExceptionalUnitGraph(method.retrieveActiveBody());
				SmartLocalDefs smd = new SmartLocalDefs(graph, new SimpleLiveLocals(graph));
				List<Unit> unitList = smd.getDefsOfAt((JimpleLocal)rightValue, searchStmt);
				
				//FIXME 缩减搜索范围
				unitList = getPreUnitList(unitList, searchStmt, method);
				
				//FIXME 只要分析处理最后一次局部变量
				Unit u = unitList.size() == 0 ? null : unitList.get(unitList.size() - 1);
				if(u != null) {
//					return sclist;
					ulist.add(u);	//把这个类局部变量的定义语句放到待分析列表中
				}
				
//				ulist.addAll(unitList);	//把这个类局部变量的定义语句放到待分析列表中
			}
			else if(rightValue instanceof ParameterRef) {		//方法参数赋值给类成员变量，这样的变量定义要从函数调用中去找
				//变量引用是方法参数，获取上次的分析语句调用
				Iterator<Edge> eit = cg.edgesInto(method);	//找到这个方法的调用点，然后依次分析
				while(eit.hasNext()) {
					Edge edge = eit.next();
					MethodOrMethodContext tmpsrcmomc = edge.getSrc();
					if(!mlist.contains(tmpsrcmomc)) {
						List<MethodOrMethodContext> newList = new ArrayList<MethodOrMethodContext>(mlist);
						newList.add(srcmomc);
						sclist.addAll(analysisActualParaInMethod((ParameterRef) rightValue, tmpsrcmomc, edge.srcUnit(), cg, level + 1, newList));
					}
				}
				
				rightValue = null;
			}
			else if(rightValue instanceof JInstanceFieldRef) {		//其它类成员变量赋值给类成员变量，将这两个类成员变量关联起来
				//如果从类成员变量中取值，则将两个类成员变量关联
				SootFieldRef ref = ((JInstanceFieldRef) rightValue).getFieldRef();
				sclist.addAll(myscene.getInstanceImpl(ref));
				
				rightValue = null;
			}
			else {
				//FIXME 遇到没有预料到的变量类型（常量 、null、强制类型转换、方法调用(非静态方法调用、静态方法调用)、数组、），如（-1, null, (String)r1, ）
				System.out.println("enconutered illegal value: " + rightValue);
				rightValue = null;
			}
			
			if(ulist.size() == 0) {
				break;
			}
			
			while(ulist.size() > 0)
			{
				Unit tmpunit = ulist.remove(0);
				searchStmt = tmpunit;
				rightValue = findRightValueInUnit(tmpunit);
				if(rightValue != null) {
					break;
				}
			}
			
			if(rightValue == null) {
				break;
			}
		}
		
		if(rightValue instanceof JNewExpr) {
			JNewExpr newexpr = (JNewExpr) rightValue;
			SootClass tgtsc = newexpr.getBaseType().getSootClass();
			sclist.add(tgtsc);
		}
		
		return sclist;
	}
	
	/**
	 * 在方法srcmomc中变量的初始化对象，变量是调用语句unit的参数pararef，它传值给类成员变量sfr（因为我们要分析sfr的实际实例化值，所以要分析调用者的参数赋值过程）
	 * @param sfr
	 * @param pararef
	 * @param srcmomc
	 * @param unit
	 * @param cg
	 */
	private void analysisSootFieldRefInMethod(SootFieldRef sfr, ParameterRef pararef, MethodOrMethodContext srcmomc, Unit unit, CallGraph cg, int level) {
		
		if(level > THRESHOLD) {
			System.out.println("can not continue because of deep level: " + level);
			return ;
		}
		
		MyScene myscene = MyScene.v();
		SootMethod method = srcmomc.method();
		
		SootClass sc = srcmomc.method().getDeclaringClass();
		if(sc.getName().startsWith("java.") || sc.getName().startsWith("android.")) {
//			System.out.println("no need to analyze system lib Class!");
			return ;
		}
		
		if(!(unit instanceof JInvokeStmt)) { //必须是函数调用语句
			return ;
		}
		
		JInvokeStmt stmt = (JInvokeStmt) unit;
		InvokeExprBox exprBox = (InvokeExprBox) stmt.getInvokeExprBox();
		
		Value value = exprBox.getValue();
		assert value instanceof InvokeExpr;
//		if(!(value instanceof InvokeExpr)) {
//			return;
//		}
		
		Value rightValue = ((InvokeExpr) value).getArg(pararef.getIndex()); 
		
		Unit searchStmt = unit;
		List<Unit> ulist = new ArrayList<Unit>();
		
		while(!(rightValue instanceof JNewExpr)) {
			if(rightValue instanceof JimpleLocal) {	//方法内局部变量赋值给类成员变量，这样的变量定义要从方法内找
				
				ExceptionalUnitGraph graph = new ExceptionalUnitGraph(method.retrieveActiveBody());
				SmartLocalDefs smd = new SmartLocalDefs(graph, new SimpleLiveLocals(graph));
				List<Unit> unitList = smd.getDefsOfAt((JimpleLocal)rightValue, searchStmt);
				
				ulist.addAll(unitList);	//把这个类局部变量的定义语句放到待分析列表中
			}
			else if(rightValue instanceof ParameterRef) {		//方法参数赋值给类成员变量，这样的变量定义要从函数调用中去找
				//变量引用是方法参数，获取上次的分析语句调用
				Iterator<Edge> eit = cg.edgesInto(method);	//找到这个方法的调用点，然后依次分析
				while(eit.hasNext()) {
					Edge edge = eit.next();
					MethodOrMethodContext tmpsrcmomc = edge.getSrc();
					analysisSootFieldRefInMethod(sfr,  (ParameterRef) rightValue, tmpsrcmomc, edge.srcUnit(), cg, level + 1);
				}
				
				rightValue = null;
			}
			else if(rightValue instanceof JInstanceFieldRef) {		//其它类成员变量赋值给类成员变量，将这两个类成员变量关联起来
				//如果从类成员变量中取值，则将两个类成员变量关联
				SootFieldRef ref = ((JInstanceFieldRef) rightValue).getFieldRef();
				myscene.addIdentityFieldRef(ref, sfr);
				
				rightValue = null;
			}
			else {
				//遇到没有预料到的变量类型
				System.out.println("enconutered illegal value: " + rightValue);
				rightValue = null;
			}
			
			if(ulist.size() == 0) {
				break;
			}
			
			while(ulist.size() > 0)
			{
				Unit tmpunit = ulist.remove(0);
				searchStmt = tmpunit;
				rightValue = findRightValueInUnit(tmpunit);
				if(rightValue != null) {
					break;
				}
			}
			
			if(rightValue == null) {
				break;
			}
		}
		
		if(rightValue instanceof JNewExpr) {
			JNewExpr newexpr = (JNewExpr) rightValue;
			SootClass tgtsc = newexpr.getBaseType().getSootClass();
			myscene.addFieldImplSootClass(sfr, tgtsc);
		}
	}
	
	private Stmt findVbInUnits(Body body, ValueBox vb) {
		PatchingChain<Unit> units = body.getUnits();
		for(Unit u:units) {
			for(ValueBox ivb:u.getUseAndDefBoxes()){
				if(ivb.equals(vb)) {
					return (Stmt) u;
				};
			}
		}
		return null;
	}
	
	/**
	 * Creates a new executor object for spawning worker threads
	 * @param numThreads The number of threads to use
	 * @return The generated executor
	 */
	private CountingThreadPoolExecutor createExecutor(int numThreads) {
		return new CountingThreadPoolExecutor
				(maxThreadNum == -1 ? numThreads : Math.min(maxThreadNum, numThreads),
				Integer.MAX_VALUE, 30, TimeUnit.SECONDS,
				new LinkedBlockingQueue<Runnable>());
	}
	
	/**
	 * Computes the path of tainted data between the source and the sink
	 * @param res The data flow tracker results
	 */
	private void computeTaintPaths(final Set<AbstractionAtSink> res) {
		IAbstractionPathBuilder builder = this.pathBuilderFactory.createPathBuilder(maxThreadNum);
    	if (computeResultPaths)
    		builder.computeTaintPaths(res);
    	else
    		builder.computeTaintSources(res);
    	this.results = builder.getResults();
    	builder.shutdown();
	}

	private Collection<SootMethod> getMethodsForSeeds(IInfoflowCFG icfg) {
		List<SootMethod> seeds = new LinkedList<SootMethod>();
		// If we have a callgraph, we retrieve the reachable methods. Otherwise,
		// we have no choice but take all application methods as an approximation
		if (Scene.v().hasCallGraph()) {
			List<MethodOrMethodContext> eps = new ArrayList<MethodOrMethodContext>(Scene.v().getEntryPoints());
			ReachableMethods reachableMethods = new ReachableMethods(Scene.v().getCallGraph(), eps.iterator(), null);
			reachableMethods.update();
			for (Iterator<MethodOrMethodContext> iter = reachableMethods.listener(); iter.hasNext();)
				seeds.add(iter.next().method());
		}
		else {
			long beforeSeedMethods = System.nanoTime();
			Set<SootMethod> doneSet = new HashSet<SootMethod>();
			for (SootMethod sm : Scene.v().getEntryPoints())
				getMethodsForSeedsIncremental(sm, doneSet, seeds, icfg);
			logger.info("Collecting seed methods took {} seconds", (System.nanoTime() - beforeSeedMethods) / 1E9);
		}
		return seeds;
	}

	private void getMethodsForSeedsIncremental(SootMethod sm,
			Set<SootMethod> doneSet, List<SootMethod> seeds, IInfoflowCFG icfg) {
		assert Scene.v().hasFastHierarchy();
		if (!sm.isConcrete() || !sm.getDeclaringClass().isApplicationClass() || !doneSet.add(sm))
			return;
		seeds.add(sm);
		for (Unit u : sm.retrieveActiveBody().getUnits()) {
			Stmt stmt = (Stmt) u;
			if (stmt.containsInvokeExpr())
				for (SootMethod callee : icfg.getCalleesOfCallAt(stmt))
					getMethodsForSeedsIncremental(callee, doneSet, seeds, icfg);
		}
	}

	
	public List<Unit> getSrc() {
		return src;
	}

	public void setSrc(List<Unit> src) {
		this.src = src;
	}

	public List<Unit> getSnk() {
		return snk;
	}

	public void setSnk(List<Unit> snk) {
		this.snk = snk;
	}

	/**
	 * Scans the given method for sources and sinks contained in it. Sinks are
	 * just counted, sources are added to the InfoflowProblem as seeds.
	 * @param sourcesSinks The SourceSinkManager to be used for identifying
	 * sources and sinks
	 * @param forwardProblem The InfoflowProblem in which to register the
	 * sources as seeds
	 * @param m The method to scan for sources and sinks
	 * @return The number of sinks found in this method
	 */
	private int scanMethodForSourcesSinks(
			final ISourceSinkManager sourcesSinks,
			InfoflowProblem forwardProblem,
			SootMethod m) {
		int sinkCount = 0;
		if (m.hasActiveBody()) {
			// Check whether this is a system class we need to ignore
			final String className = m.getDeclaringClass().getName();
			if (ignoreFlowsInSystemPackages && SystemClassHandler.isClassInSystemPackage(className))
				return sinkCount;
			
			// Look for a source in the method. Also look for sinks. If we
			// have no sink in the program, we don't need to perform any
			// analysis
			PatchingChain<Unit> units = m.getActiveBody().getUnits();
			for (Unit u : units) {
				Stmt s = (Stmt) u;
				if (sourcesSinks.getSourceInfo(s, iCfg) != null) {
					forwardProblem.addInitialSeeds(u, Collections.singleton(forwardProblem.zeroValue()));
					src.add(u);
					logger.debug("Source found: {}", u);
				}
				if (sourcesSinks.isSink(s, iCfg)) {
					snk.add(u);
		            logger.debug("Sink found: {}", u);
					sinkCount++;
				}
			}
			
		}
		return sinkCount;
	}
	
	@Override
	public InfoflowResults getResults() {
		return results;
	}

	@Override
	public boolean isResultAvailable() {
		if (results == null) {
			return false;
		}
		return true;
	}
	
	public static int getAccessPathLength() {
		return accessPathLength;
	}
	
	/**
	 * Sets the maximum depth of the access paths. All paths will be truncated
	 * if they exceed the given size.
	 * @param accessPathLength the maximum value of an access path. If it gets longer than
	 *  this value, it is truncated and all following fields are assumed as tainted 
	 *  (which is imprecise but gains performance)
	 *  Default value is 5.
	 */
	public static void setAccessPathLength(int accessPathLength) {
		MyInfoflow.accessPathLength = accessPathLength;
	}
	
	/**
	 * Sets whether results (source-to-sink connections) that only differ in their
	 * propagation paths shall be merged into a single result or not.
	 * @param pathAgnosticResults True if two results shall be regarded as equal
	 * if they connect the same source and sink, even if their propagation paths
	 * differ, otherwise false
	 */
	public static void setPathAgnosticResults(boolean pathAgnosticResults) {
		MyInfoflow.pathAgnosticResults = pathAgnosticResults;
	}
	
	/**
	 * Gets whether results (source-to-sink connections) that only differ in their
	 * propagation paths shall be merged into a single result or not.
	 * @return True if two results shall be regarded as equal if they connect the
	 * same source and sink, even if their propagation paths differ, otherwise
	 * false
	 */
	public static boolean getPathAgnosticResults() {
		return MyInfoflow.pathAgnosticResults;
	}
	
	/**
	 * Gets whether recursive access paths shall be reduced, e.g. whether we
	 * shall propagate a.[next].data instead of a.next.next.data.
	 * @return True if recursive access paths shall be reduced, otherwise false
	 */
	public static boolean getUseRecursiveAccessPaths() {
		return useRecursiveAccessPaths;
	}

	/**
	 * Sets whether recursive access paths shall be reduced, e.g. whether we
	 * shall propagate a.[next].data instead of a.next.next.data.
	 * @param useRecursiveAccessPaths True if recursive access paths shall be
	 * reduced, otherwise false
	 */
	public static void setUseRecursiveAccessPaths(boolean useRecursiveAccessPaths) {
		MyInfoflow.useRecursiveAccessPaths = useRecursiveAccessPaths;
	}
	
	/**
	 * Adds a handler that is called when information flow results are available
	 * @param handler The handler to add
	 */
	public void addResultsAvailableHandler(ResultsAvailableHandler handler) {
		this.onResultsAvailable.add(handler);
	}
	
	/**
	 * Adds a handler which is invoked whenever a taint is propagated
	 * @param handler The handler to be invoked when propagating taints
	 */
	public void addTaintPropagationHandler(TaintPropagationHandler handler) {
		this.taintPropagationHandlers.add(handler);
	}
	
	/**
	 * Removes a handler that is called when information flow results are available
	 * @param handler The handler to remove
	 */
	public void removeResultsAvailableHandler(ResultsAvailableHandler handler) {
		onResultsAvailable.remove(handler);
	}
	
	@Override
	public void setIPCManager(IIPCManager ipcManager) {
	    this.ipcManager = ipcManager;
	}

	public String getmGraph() {
		return mGraph;
	}

	public void setmGraph(String mGraph) {
		this.mGraph = mGraph;
	}
}
