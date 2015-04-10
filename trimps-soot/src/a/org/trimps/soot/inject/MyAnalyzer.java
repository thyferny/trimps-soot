package a.org.trimps.soot.inject;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.UUID;

import org.xmlpull.v1.XmlPullParserException;

import soot.jimple.infoflow.IInfoflow.CallgraphAlgorithm;
import soot.jimple.infoflow.android.AndroidSourceSinkManager.LayoutMatchingMode;
import soot.jimple.infoflow.android.axml.AXmlNode;
import soot.jimple.infoflow.android.data.AndroidMethod;
import soot.jimple.infoflow.taintWrappers.EasyTaintWrapper;
import soot.jimple.infoflow.taintWrappers.ITaintPropagationWrapper;

import com.mysql.jdbc.Driver;

public class MyAnalyzer {
	static boolean generate = false;

	private static boolean stopAfterFirstFlow = false;
	private static boolean implicitFlows = false;
	private static boolean staticTracking = true;
	private static boolean enableCallbacks = true;
	private static boolean enableExceptions = true;
	private static int accessPathLength = 5;
	private static LayoutMatchingMode layoutMatchingMode = LayoutMatchingMode.MatchSensitiveOnly;
	private static boolean flowSensitiveAliasing = true;
	private static boolean computeResultPaths = true;
	private static boolean aggressiveTaintWrapper = false;

	private static CallgraphAlgorithm callgraphAlgorithm = CallgraphAlgorithm.AutomaticSelection;
	private static String SDKs = "/home/thyferny/android-sdks/platforms";

	static LinkedList<String> permissions = new LinkedList<String>();
	static List<String> activities = new ArrayList<String>();
	static String packageName = "";
	static String applicationName = "";
	static boolean[] permissionIndex;
	
	static LinkedList<String> srcPoints = new LinkedList<String>();
	static LinkedList<String> snkPoints = new LinkedList<String>();
	static int[] srcCharacter;
	static int[] snkCharacter;
	
	static {
		try {
			File f = new File("/home/thyferny/AndroidPermissions");
			InputStream is = new FileInputStream(f);
			InputStreamReader isr = new InputStreamReader(is);
			BufferedReader br = new BufferedReader(isr);
			String permission = "";
			while ((permission = br.readLine()) != null) {
				if (permission.startsWith("android.permission")||permission.startsWith("com.android")||permission.startsWith("com.google")) {
					permissions.add(permission);
				}
			}
			br.close();
			isr.close();
			is.close();
			permissionIndex = new boolean[permissions.size()];
			Arrays.fill(permissionIndex, false);
			/*------------------------------*/
			f = new File("SourcesAndSinks.txt");
			is = new FileInputStream(f);
			isr = new InputStreamReader(is);
			br = new BufferedReader(isr);
			String ss = "";
			while ((ss = br.readLine()) != null) {
				if (ss.startsWith("<")) {
					if(ss.endsWith("_SOURCE_")){
						srcPoints.add(ss.split("> ")[0]+">");
					}else if(ss.endsWith("_SINK_")){
						snkPoints.add(ss.split("> ")[0]+">");
					}
				}
			}
			br.close();
			isr.close();
			is.close();
			srcCharacter = new int[srcPoints.size()];
			snkCharacter = new int[snkPoints.size()];
			Arrays.fill(srcCharacter, 0);
			Arrays.fill(snkCharacter, 0);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public static void main(String[] args) throws IOException, SQLException {
//		static String apkFilePath = "/home/thyferny/FakeCall_3.2.3_323.apk";
		if(generate){
			for(File f:new File("/home/thyferny/300TEST").listFiles()){
				singalApkRunner(f.getAbsolutePath());
			}
		}else{
			for(File f:new File("/home/thyferny/1TEST").listFiles()){
				singalApkGeneralMatcher(f.getAbsolutePath());
			}
		}
	}
	
	private static void singalApkGeneralMatcher(String apkFilePath) throws SQLException {
		String signInfo = MyUtil.getApkSignInfo(apkFilePath);
		String character1_1 = "";
		if("".equals(signInfo)){
			character1_1 = "";
		}else{
			character1_1 = MyUtil.md5(signInfo);
		}
		
		String character1_2 = MyUtil.md5(new File(apkFilePath));
//		System.out.println(character1_1);
//		System.out.println(character1_2);
		// 特征1提取完成
		String character2_1 = "";
		String character2_2 = "";
		MyAXMLPrinter2Parser parser = new MyAXMLPrinter2Parser();
		try {
			parser.parseFile(apkFilePath);
			AXmlNode root = parser.getRoot();
			analyseNode(root);
			Collections.sort(activities);
			character2_1 = MyUtil.md5(MyUtil.listToString(activities));
			character2_2 = MyUtil.toHexString(permissionIndex);
		} catch (Exception e) {
//			e.printStackTrace();
		}
		
//		System.out.println(character2_1);
//		System.out.println(character2_2);
		// 特征2提取完成
		String character3_1;
		String character3_2;
		try{
			runAnalysis(apkFilePath, SDKs);
			character3_1 = MyUtil.md5(Arrays.toString(srcCharacter));
			character3_2 = MyUtil.md5(Arrays.toString(snkCharacter));
		}catch(Throwable th){
//			th.printStackTrace();
			character3_1 = "";
			character3_2 = "";
		}
		
		// 特征3提取完成
		Connection conn  = mysqlConnection();
		if(conn!=null){
			Statement st = conn.createStatement();
			ResultSet rs = st.executeQuery("select * from signature where sig11=\'"+character1_1+"\'");
			while(rs.next()){
				System.out.println("find " +apkFilePath +" has cert same with "+rs.getString("uuid"));
				break;
			}
			rs = st.executeQuery("select * from signature where sig12=\'"+character1_2+"\'");
			while(rs.next()){
				System.out.println("find " +apkFilePath +" same with "+rs.getString("uuid"));
				break;
			}
			rs = st.executeQuery("select * from signature where sig21=\'"+character2_1+"\'");
			while(rs.next()){
				System.out.println("find " +apkFilePath +" same activity structure with "+rs.getString("uuid"));
				break;
			}
			rs = st.executeQuery("select * from signature where sig22=\'"+character2_2+"\'");
			while(rs.next()){
				System.out.println("find " +apkFilePath +" same permission with "+rs.getString("uuid"));
				break;
			}
			rs = st.executeQuery("select * from signature where sig31=\'"+character3_1+"\'");
			while(rs.next()){
				System.out.println("find " +apkFilePath +" same permission with "+rs.getString("uuid"));
				break;
			}
			rs = st.executeQuery("select * from signature where sig32=\'"+character3_2+"\'");
			while(rs.next()){
				System.out.println("find " +apkFilePath +" same permission with "+rs.getString("uuid"));
				break;
			}
			st.close();
		}
		System.out.println("----------------------------------------------");
	}

	private static void singalApkRunner(String apkFilePath) throws SQLException {
		String signInfo = MyUtil.getApkSignInfo(apkFilePath);
		String character1_1 = "";
		if("".equals(signInfo)){
			character1_1 = "";
		}else{
			character1_1 = MyUtil.md5(signInfo);
		}
		
		String character1_2 = MyUtil.md5(new File(apkFilePath));
//		System.out.println(character1_1);
//		System.out.println(character1_2);
		// 特征1提取完成
		String character2_1 = "";
		String character2_2 = "";
		MyAXMLPrinter2Parser parser = new MyAXMLPrinter2Parser();
		try {
			parser.parseFile(apkFilePath);
			AXmlNode root = parser.getRoot();
			analyseNode(root);
			Collections.sort(activities);
			character2_1 = MyUtil.md5(MyUtil.listToString(activities));
			character2_2 = MyUtil.toHexString(permissionIndex);
		} catch (Exception e) {
//			e.printStackTrace();
		}
//		System.out.println(character2_1);
//		System.out.println(character2_2);
		// 特征2提取完成
		String character3_1;
		String character3_2;
		try{
			runAnalysis(apkFilePath, SDKs);
			character3_1 = MyUtil.md5(Arrays.toString(srcCharacter));
			character3_2 = MyUtil.md5(Arrays.toString(snkCharacter));
		}catch(Throwable th){
//			th.printStackTrace();
			character3_1 = "";
			character3_2 = "";
		}
		
		// 特征3提取完成
		Connection conn  = mysqlConnection();
		if(conn!=null){
			PreparedStatement ps = conn.prepareStatement("insert into signature values(?,?,?,?,?,?,?,?)");
			ps.setString(1, UUID.randomUUID().toString());
			ps.setString(2, character1_1);
			ps.setString(3, character1_2);
			ps.setString(4, character2_1);
			ps.setString(5, character2_2);
			ps.setString(6, character3_1);
			ps.setString(7, character3_2);
			ps.setBoolean(8, true);
			ps.execute();
		}
	}

	public static Connection mysqlConnection(){
		StringBuffer url = new StringBuffer();
		String host = "127.0.0.1";
		String database = "apksignature";
		String user = "root";
		String port = "3306";
		String passwd = "root";
		url.append("jdbc:mysql://").append(host).append(":").append(port).append("/").append(database).append("?user=").append(user).append("&password=").append(passwd).append("&characterEncoding=utf-8");
		Connection conn = null;
		try {
			new Driver();
			conn = DriverManager.getConnection(url.toString());
		} catch (SQLException e) {
			e.printStackTrace();
		}
		return conn;
	}
	private static void analyseNode(AXmlNode node) {
		analyzeSingleNode(node);
		if (node.getChildren().size() > 0) {
			for (AXmlNode child : node.getChildren()) {
				analyseNode(child);
			}
		}
	}

	private static void analyzeSingleNode(AXmlNode node) {
		try {
			if (node.getParent() == null) {
				packageName = node.getAttribute("package").getValue().toString();
			}
			if (node.getTag().equals("uses-permission")) {
				int index = permissions.indexOf(node.getAttribute("name").getValue().toString());
				if (index != -1) {
					permissionIndex[index] = true;
				} else {
//					"unkown permission type:" +
//					System.err.println( node.getAttribute("name").getValue().toString());
				}
			} else if (node.getTag().equals("application")) {
				applicationName = node.getAttribute("name").getValue().toString();
			} else if (node.getTag().equals("activity")) {
				activities.add(node.getAttribute("name").getValue().toString());
			}
		} catch (Exception e) {
		}
	}

	private static void runAnalysis(final String fileName, final String androidJar) {
		try {
			final long beforeRun = System.nanoTime();

			final MySetupApplication app;
			app = new MySetupApplication(androidJar, fileName);
			app.setStopAfterFirstFlow(stopAfterFirstFlow);
			app.setEnableImplicitFlows(implicitFlows);
			app.setEnableStaticFieldTracking(staticTracking);
			app.setEnableCallbacks(enableCallbacks);
			app.setEnableExceptionTracking(enableExceptions);
			app.setAccessPathLength(accessPathLength);
			app.setLayoutMatchingMode(layoutMatchingMode);
			app.setFlowSensitiveAliasing(flowSensitiveAliasing);
			app.setComputeResultPaths(computeResultPaths);

			final ITaintPropagationWrapper taintWrapper;

			final EasyTaintWrapper easyTaintWrapper;
			if (new File("../soot-infoflow/EasyTaintWrapperSource.txt").exists())
				easyTaintWrapper = new EasyTaintWrapper("../soot-infoflow/EasyTaintWrapperSource.txt");
			else
				easyTaintWrapper = new EasyTaintWrapper("EasyTaintWrapperSource.txt");
			easyTaintWrapper.setAggressiveMode(aggressiveTaintWrapper);
			taintWrapper = easyTaintWrapper;

			app.setTaintWrapper(taintWrapper);
			app.calculateSourcesSinksEntrypoints("SourcesAndSinks.txt");
			Set<AndroidMethod> source = app.getSources();
			Set<AndroidMethod> sink = app.getSinks();
			for(AndroidMethod src :source){
				String method = "<"+src.getClassName()+": "+src.getSubSignature()+">";
				int index = srcPoints.indexOf(method);
				if(index==-1){
					System.err.println("ERROR:"+method);
				}else{
					srcCharacter[index]++;
				}
			}
			for(AndroidMethod snk :sink){
				String method = "<"+snk.getClassName()+": "+snk.getSubSignature()+">";
				int index = snkPoints.indexOf(method);
				if(index==-1){
					System.err.println("ERROR:"+method);
				}else{
					snkCharacter[index]++;
				}
			}
			System.out.println("Analysis has run for " + (System.nanoTime() - beforeRun) / 1E9 + " seconds");
		} catch (IOException ex) {
			System.err.println("Could not read file: " + ex.getMessage());
			ex.printStackTrace();
			throw new RuntimeException(ex);
		} catch (XmlPullParserException ex) {
			System.err.println("Could not read Android manifest file: " + ex.getMessage());
			ex.printStackTrace();
			throw new RuntimeException(ex);
		}
	}
}
