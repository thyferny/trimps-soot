package a.org.trimps.soot.inject;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileWriter;
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
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.UUID;

import org.xmlpull.v1.XmlPullParserException;

import soot.Unit;
import soot.jimple.infoflow.android.AndroidSourceSinkManager.LayoutMatchingMode;
import soot.jimple.infoflow.android.axml.AXmlNode;
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

	private static String SDKs = "E:/sdk/platforms";

	static LinkedList<String> permissions = new LinkedList<String>();
	static List<String> activities = new ArrayList<String>();
	static String packageName = "";
	static String applicationName = "";
	static boolean[] permissionIndex;

	static LinkedList<String> srcPoints = new LinkedList<String>();
	static LinkedList<String> snkPoints = new LinkedList<String>();
	static int[] srcCharacter;
	static int[] snkCharacter;
	static String lineSep ="\n";
	static String resultFile = "E:/MyAnalyzer.result1";

	static {
		try {
			File f = new File("AndroidPermissions");
			InputStream is = new FileInputStream(f);
			InputStreamReader isr = new InputStreamReader(is);
			BufferedReader br = new BufferedReader(isr);
			String permission = "";
			while ((permission = br.readLine()) != null) {
				if (permission.startsWith("android.permission") || permission.startsWith("com.android") || permission.startsWith("com.google")) {
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
					if (ss.endsWith("_SOURCE_")) {
						srcPoints.add(ss.split("> ")[0] + ">");
					} else if (ss.endsWith("_SINK_")) {
						snkPoints.add(ss.split("> ")[0] + ">");
					}
				}
			}
			br.close();
			isr.close();
			is.close();

			srcCharacter = new int[srcPoints.size()];
			snkCharacter = new int[snkPoints.size()];
			
			lineSep = System.getProperty("line.separator", "\n");
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public static void main(String[] args) throws IOException, SQLException {
		// static String apkFilePath = "/home/thyferny/FakeCall_3.2.3_323.apk";
		if (generate) {
			updateDataBase();
			for (File f : new File("F:/home/300TEST").listFiles()) {
				singalApkRunner(f.getAbsolutePath());
			}
		} else {
			for (File f : new File("F:/home/1TEST").listFiles()) {
				singalApkGeneralMatcher(f.getAbsolutePath());
			}
		}
	}

//	public static void kMeansDriver() throws SQLException {
//		Statement st = mysqlConnection().createStatement();
//		ResultSet rs = st.executeQuery("select * from apksrc");
//		ArrayList<double[]> all = new ArrayList<>();
//		while (rs.next()) {
//			String val = rs.getString("val");
//			String[] tmp = val.replaceAll("\\[", "").replaceAll("\\]", "").split(",");
//			double[] vec = new double[tmp.length - 1];
//			for (int i = 0; i < vec.length; i++) {
//				vec[i] = Double.parseDouble(tmp[i]);
//			}
//			all.add(vec);
//		}
//		int len = all.get(0).length;
//		// 划分为10个簇，质心移动小于1E-8时终止迭代，重复运行20次
//		double kSA = Double.MAX_VALUE;
//		int fail = 0;
//		double estimateK = Math.sqrt(all.size()) * 2;
//		int k;
//		for (k = 1; k < estimateK; k++) {
//			System.out.println("k=" + k);
//			KMeansEngine km = new KMeansEngine(k, 1E-10, 8, len);
//			int index = 0;
//			double minsa = Double.MAX_VALUE;
//			for (int i = 0; i < km.repeat; i++) {
//				double ss = km.run(i, all, len);
//				if (ss < minsa) {
//					minsa = ss;
//					index = i;
//				}
//			}
//			System.out.println("最好的结果是第" + index + "次。" + "SS:" + minsa);
//			System.out.println("-------------------------------------------------------");
//			if (kSA < minsa) {//
//				fail++;
//			} else {
//				kSA = minsa;
//			}
//			if (fail > 5) {
//				break;
//			}
//		}
//		System.out.println("该批数据最好聚未" + k + "类");
//	}
	
	public static String minDistApkMacter(String apkFilePath) throws SQLException, IOException {
		String minDistMd5 = "";
		Statement st = mysqlConnection().createStatement();
		ResultSet rs = st.executeQuery("select * from kmeans");
		Map<String,double[]> all = new HashMap<>();
		List<Double> avg = new ArrayList<>();
		while (rs.next()) {
			String val = rs.getString("center");
			String[] tmp = val.replaceAll("\\[", "").replaceAll("\\]", "").split(",");
			double[] vec = new double[tmp.length - 1];
			for (int i = 0; i < vec.length; i++) {
				vec[i] = Double.parseDouble(tmp[i]);
			}
			all.put(rs.getString("uuid"),vec);
			avg.add(rs.getDouble("avg"));
		}
		double minDst = Double.MAX_VALUE;
		for(String uuid:all.keySet()){
			double[] vec = all.get(uuid);
			if(minDst>MyUtil.calEditDist(srcCharacter, vec, vec.length)){
				minDst = MyUtil.calEditDist(srcCharacter, vec, vec.length);
				minDistMd5 = uuid;
			}
		}
//		rs = st.executeQuery("select name from apkname where uuid in (select uuid from signature where sig31=\'"+minDistMd5+"\')");
		FileWriter fw = new FileWriter(resultFile, true);
		fw.write("分析文件:"+apkFilePath+lineSep);
		fw.write("最近值:"+minDst+lineSep);
		fw.write("所属中心UUID:"+minDistMd5+lineSep);
//		while (rs.next()) {
//			String val = rs.getString("name");
//			fw.write("最近APK:"+val+lineSep);
//		}
		fw.write("----------------------------------------------------------------------------------------"+lineSep);
		fw.flush();
		fw.close();
		return minDistMd5;
	}

	static void updateDataBase() throws SQLException {
		Statement st = mysqlConnection().createStatement();
		st.execute("delete from signature");
		st.execute("drop table if exists apksrc");
		st.execute("create table apksrc(md5 text,val text)");
		st.execute("drop table if exists apksnk");
		st.execute("create table apksnk(md5 text,val text)");
		st.execute("drop table if exists apkname");
		st.execute("create table apkname(uuid text,name text)");
	}

	private static void singalApkGeneralMatcher(String apkFilePath) throws SQLException, IOException {
		String signInfo = MyUtil.getApkSignInfo(apkFilePath);
		String character1_1 = "";
		if ("".equals(signInfo)) {
			character1_1 = "";
		} else {
			character1_1 = MyUtil.md5(signInfo);
		}

		String character1_2 = MyUtil.md5(new File(apkFilePath));
		// System.out.println(character1_1);
		// System.out.println(character1_2);
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
			// e.printStackTrace();
		}

		// System.out.println(character2_1);
		// System.out.println(character2_2);
		// 特征2提取完成
		String character3_1;
		String character3_2;
		try {
			runAnalysis(apkFilePath, SDKs);
			character3_1 = MyUtil.md5(Arrays.toString(srcCharacter));
			character3_2 = MyUtil.md5(Arrays.toString(snkCharacter));
		} catch (Throwable th) {
			// th.printStackTrace();
			character3_1 = "";
			character3_2 = "";
		}

		// 特征3提取完成
		FileWriter fw = new FileWriter(resultFile, true);
		Connection conn = mysqlConnection();
		if (conn != null) {
			Statement st = conn.createStatement();
			ResultSet rs = st.executeQuery("select name from apkname where uuid in (select uuid from signature where sig11=\'" + character1_1 + "\')");
			while (rs.next()) {
				fw.write("find " + apkFilePath + " has cert same with " + rs.getString("name")+lineSep);
			}
			rs = st.executeQuery("select name from apkname where uuid in (select uuid from signature where sig12=\'" + character1_2 + "\')");
			while (rs.next()) {
				fw.write("find " + apkFilePath + " same with " + rs.getString("name")+lineSep);
			}
			rs = st.executeQuery("select name from apkname where uuid in (select uuid from signature where sig21=\'" + character2_1 + "\')");
			while (rs.next()) {
				fw.write("find " + apkFilePath + " same activity structure with " + rs.getString("name")+lineSep);
			}
			rs = st.executeQuery("select name from apkname where uuid in (select uuid from signature where sig22=\'" + character2_2 + "\')");
			while (rs.next()) {
				fw.write("find " + apkFilePath + " same permission with " + rs.getString("name")+lineSep);
			}
			rs = st.executeQuery("select name from apkname where uuid in (select uuid from signature where sig31=\'" + character3_1 + "\')");
			while (rs.next()) {
				fw.write("find " + apkFilePath + " same permission with " + rs.getString("name")+lineSep);
			}
			rs = st.executeQuery("select name from apkname where uuid in (select uuid from signature where sig32=\'" + character3_2 + "\')");
			while (rs.next()) {
				fw.write("find " + apkFilePath + " same permission with " + rs.getString("name")+lineSep);
			}
			st.close();
		}
		fw.write("**************************************************************************"+lineSep);
		fw.flush();
		fw.close();
		minDistApkMacter(apkFilePath);
		
	}

	private static void singalApkRunner(String apkFilePath) throws SQLException {
		String signInfo = MyUtil.getApkSignInfo(apkFilePath);
		String character1_1 = "";
		if ("".equals(signInfo)) {
			character1_1 = "";
		} else {
			character1_1 = MyUtil.md5(signInfo);
		}

		String character1_2 = MyUtil.md5(new File(apkFilePath));
		// System.out.println(character1_1);
		// System.out.println(character1_2);
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
			// e.printStackTrace();
		}
		// System.out.println(character2_1);
		// System.out.println(character2_2);
		// 特征2提取完成
		String character3_1;
		String character3_2;
		Arrays.fill(srcCharacter, 0);
		Arrays.fill(snkCharacter, 0);
		try {
			runAnalysis(apkFilePath, SDKs);
			character3_1 = MyUtil.md5(Arrays.toString(srcCharacter));
			character3_2 = MyUtil.md5(Arrays.toString(snkCharacter));
		} catch (Throwable th) {
			// th.printStackTrace();
			character3_1 = "";
			character3_2 = "";
		}

		// 特征3提取完成
		String uuid = UUID.randomUUID().toString();
		Connection conn = mysqlConnection();
		if (conn != null) {
			PreparedStatement ps1 = conn.prepareStatement("insert into signature values(?,?,?,?,?,?,?,?)");
			ps1.setString(1, uuid);
			ps1.setString(2, character1_1);
			ps1.setString(3, character1_2);
			ps1.setString(4, character2_1);
			ps1.setString(5, character2_2);
			ps1.setString(6, character3_1);
			ps1.setString(7, character3_2);
			ps1.setBoolean(8, true);
			ps1.execute();

			PreparedStatement ps2 = conn.prepareStatement("insert into apkname values(?,?)");
			ps2.setString(1, uuid);
			ps2.setString(2, apkFilePath);
			ps2.execute();

			if (!"".equals(character3_1) && !"".equals(character3_1)) {
				PreparedStatement ps3 = conn.prepareStatement("insert into apksrc values(?,?)");
				ps3.setString(1, MyUtil.md5(Arrays.toString(srcCharacter)));
				ps3.setString(2, Arrays.toString(srcCharacter));
				ps3.execute();

				PreparedStatement ps4 = conn.prepareStatement("insert into apksnk values(?,?)");
				ps4.setString(1, MyUtil.md5(Arrays.toString(snkCharacter)));
				ps4.setString(2, Arrays.toString(snkCharacter));
				ps4.execute();
			}

		}
	}

	public static Connection mysqlConnection() {
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
					// "unkown permission type:" +
					// System.err.println(
					// node.getAttribute("name").getValue().toString());
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

			app.runInfoflow(null);
			for (Unit sink : app.getSnk()) {
				int snkIndex = MyUtil.myIndexInList(snkPoints, sink.toString());
				if (snkIndex == -1) {
					System.err.println("ERROR Unkown Sink:" + sink);
				} else {
					snkCharacter[snkIndex]++;
				}
			}
			for (Unit source : app.getSrc()) {
				int srcIndex = MyUtil.myIndexInList(srcPoints, source.toString());
				if (srcIndex == -1) {
					System.err.println("ERROR Unkown Source:" + source.toString());
				} else {
					srcCharacter[srcIndex]++;
				}
			}

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
