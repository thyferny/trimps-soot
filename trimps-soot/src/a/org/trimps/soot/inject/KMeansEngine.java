package a.org.trimps.soot.inject;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.Random;
import java.util.UUID;

import com.mysql.jdbc.Driver;

public class KMeansEngine {
 
    int k; // 指定划分的簇数
    double mu; // 迭代终止条件，当各个新质心相对于老质心偏移量小于mu时终止迭代
    double[][] center; // 上一次各簇质心的位置
    Map<String, Integer> cidMap = new HashMap<>();
    int repeat; // 重复运行次数
    double[] crita; // 存放每次运行的满意度
    
 
    public KMeansEngine(int k, double mu, int repeat, int len) {
        this.k = k;
        this.mu = mu;
        this.repeat = repeat;
        center = new double[k][];
        for (int i = 0; i < k; i++)
            center[i] = new double[len];
        crita = new double[repeat];
    }
 
    // 初始化k个质心，每个质心是len维的向量，每维均在left--right之间
    public void initCenter(int len, Map<String, double[]> all) {
        Random random = new Random(System.currentTimeMillis());
        int[] count = new int[k]; // 记录每个簇有多少个元素
       	for(String key:all.keySet()){
       		double[] vec = all.get(key);
            int id = random.nextInt(10000)%k;
            count[id]++;
            for (int i = 0; i < len; i++)
                center[id][i] += vec[i];
        }
        for (int i = 0; i < k; i++) {
            for (int j = 0; j < len; j++) {
                center[i][j] /= count[i];
            }
        }
    }
 
    // 把数据集中的每个点归到离它最近的那个质心
    public void classify(Map<String, double[]> all) {
    	for(String key:all.keySet()){
    		double[] vector = all.get(key);
            int len = vector.length;
            int index = 0;
            double neardist = Double.MAX_VALUE;
            for (int i = 0; i < k; i++) {
                // double dist = Global.calEuraDist(vector, center[i], len);
                // //使用欧氏距离
                double dist = MyUtil.calEditDist(vector, center[i], len); // 使用编辑距离
                if (dist < neardist) {
                    neardist = dist;
                    index = i;
                }
            }
            cidMap.put(key, index);
        }
    }
 
    // 重新计算每个簇的质心，并判断终止条件是否满足，如果不满足更新各簇的质心,如果满足就返回true.len是数据的维数
    public boolean calNewCenter(Map<String, double[]> all, int len) {
        boolean end = true;
        int[] count = new int[k]; // 记录每个簇有多少个元素
        double[][] sum = new double[k][];
        for (int i = 0; i < k; i++)
            sum[i] = new double[len];
        for(String key:all.keySet()){
            int id = cidMap.get(key);
            count[id]++;
            for (int i = 0; i < len; i++)
                sum[id][i] += all.get(key)[i];
        }
        for (int i = 0; i < k; i++) {
            if (count[i] != 0) {
                for (int j = 0; j < len; j++) {
                    sum[i][j] /= count[i];
                }
            }
            // 簇中不包含任何点,及时调整质心
            else {
                int a=(i+1)%k;
                int b=(i+3)%k;
                int c=(i+5)%k;
                for (int j = 0; j < len; j++) {
                    center[i][j] = (center[a][j]+center[b][j]+center[c][j])/3;
                }
            }
        }
        for (int i = 0; i < k; i++) {
            // 只要有一个质心需要移动的距离超过了mu，就返回false
            // if (Global.calEuraDist(sum[i], center[i], len) >= mu) { //使用欧氏距离
            if (MyUtil.calEditDist(sum[i], center[i], len) >= mu) { // 使用编辑距离
                end = false;
                break;
            }
        }
        if (!end) {
            for (int i = 0; i < k; i++) {
                for (int j = 0; j < len; j++)
                    center[i][j] = sum[i][j];
            }
        }
        return end;
    }
 
    // 计算各簇内数据和方差的加权平均，得出本次聚类的满意度.len是数据的维数
    public double getSati(Map<String, double[]> all, int len) {
        double satisfy = 0.0;
        int[] count = new int[k];
        double[] ss = new double[k];
        for(String key:all.keySet()){
            int id = cidMap.get(key);
            count[id]++;
            for (int i = 0; i < len; i++)
                ss[id] += Math.pow(all.get(key)[i] - center[id][i], 2.0);
        }
        for (int i = 0; i < k; i++) {
            satisfy += count[i] * ss[i];
        }
        return satisfy;
    }
    
    public double[] getAvg(Map<String, double[]> all, int len) {
        double[] avg = new double[k];
        int[] count = new int[k];
        double[] ss = new double[k];
        for(String key:all.keySet()){
            int id = cidMap.get(key);
            count[id]++;
            for (int i = 0; i < len; i++)
                ss[id] += Math.pow(all.get(key)[i] - center[id][i], 2.0);
        }
        for (int i = 0; i < k; i++) {
        	avg[i]= ss[i]/count[i];
        }
        return avg;
    }
 
    public double run(int round, Map<String, double[]> all, int len) {
        System.out.println("第" + round + "次运行");
        initCenter(len,all);
        classify(all);
        while (!calNewCenter(all, len)) {
            classify(all);
        }
        //datasource.printResult(datasource, k);
        double ss = getSati(all, len);
        System.out.println("加权方差：" + ss);
        return ss;
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
    public static void main(String[] args) throws SQLException {
    	Connection conn = mysqlConnection();
    	Statement st = conn.createStatement();
		ResultSet rs = st.executeQuery("select * from apksrc");
		Map<String,double[]> all = new HashMap<>();
		int len = 0;
		while (rs.next()) {
			String val = rs.getString("val");
			String[] tmp = val.replaceAll("\\[", "").replaceAll("\\]", "").split(",");
			double[] vec = new double[tmp.length - 1];
			for (int i = 0; i < vec.length; i++) {
				vec[i] = Double.parseDouble(tmp[i]);
			}
			all.put(rs.getString("md5"),vec);
			len = vec.length;
		}
//		 = all.get(0).length;
		// 划分为10个簇，质心移动小于1E-8时终止迭代，重复运行20次
		double kSA = Double.MAX_VALUE;
//		int fail = 0;
//		double estimateK = Math.sqrt(all.size()) * 2;
		
		double[][] fcenter = null; // 上一次各簇质心的位置
	    Map<String, Integer> fcidMap = new HashMap<>();
	    double[] avg = null;
	    
		int k = 22;
//		for (k = 1; k < estimateK; k++) {
			System.out.println("k=" + k);
			KMeansEngine km = new KMeansEngine(k, 1E-10, 20, len);
			int index = 0;
			double minsa = Double.MAX_VALUE;
			for (int i = 0; i < km.repeat; i++) {
				double ss = km.run(i, all, len);
				if (ss < minsa) {
					minsa = ss;
					index = i;
					fcenter = km.center;
					fcidMap = km.cidMap;
					avg = km.getAvg(all, len);
				}
			}
			System.out.println("最好的结果是第" + index + "次。" + "SS:" + minsa);
			System.out.println("-------------------------------------------------------");
//			if (kSA < minsa) {//
//				fail++;
//			} else {
//				kSA = minsa;
//			}
//			if (fail > 5) {
//				break;
//			}
//		}
		System.out.println("该批数据最好聚未" + k + "类");
		st.execute("drop table if exists kmeans");
		st.execute("create table kmeans(uuid text,center text,avg double)");
		for(int i=0;i<k;i++){
			PreparedStatement ps1 = conn.prepareStatement("insert into kmeans values(?,?,?)");
			ps1.setString(1, UUID.randomUUID().toString());
			ps1.setString(2, Arrays.toString(fcenter[i]));
			ps1.setDouble(3, avg[i]);
			ps1.execute();
		}
    }
}