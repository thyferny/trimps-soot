package a.org.trimps.soot.inject;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Random;

import com.mysql.jdbc.Driver;

public class KMeansEngine {
 
    int k; // 指定划分的簇数
    double mu; // 迭代终止条件，当各个新质心相对于老质心偏移量小于mu时终止迭代
    double[][] center; // 上一次各簇质心的位置
    int repeat; // 重复运行次数
    double[] crita; // 存放每次运行的满意度
    Map<Integer, Integer> cidMap = new HashMap<>();
 
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
    public void initCenter(int len, ArrayList<double[]> all) {
        Random random = new Random(System.currentTimeMillis());
        int[] count = new int[k]; // 记录每个簇有多少个元素
       	for(double[] vec:all){
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
    public void classify(ArrayList<double[]> all) {
    	int id = 0;
    	for(double[] vector:all){
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
            cidMap.put(id, index);
            id++;
        }
    }
 
    // 重新计算每个簇的质心，并判断终止条件是否满足，如果不满足更新各簇的质心,如果满足就返回true.len是数据的维数
    public boolean calNewCenter(ArrayList<double[]> all, int len) {
        boolean end = true;
        int[] count = new int[k]; // 记录每个簇有多少个元素
        double[][] sum = new double[k][];
        for (int i = 0; i < k; i++)
            sum[i] = new double[len];
        for(int j = 0;j<all.size();j++){
            int id = cidMap.get(j);
            count[id]++;
            for (int i = 0; i < len; i++)
                sum[id][i] += all.get(j)[i];
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
    public double getSati(ArrayList<double[]> all, int len) {
        double satisfy = 0.0;
        int[] count = new int[k];
        double[] ss = new double[k];
        for(int j = 0;j<all.size();j++){
            int id = cidMap.get(j);
            count[id]++;
            for (int i = 0; i < len; i++)
                ss[id] += Math.pow(all.get(j)[i] - center[id][i], 2.0);
        }
        for (int i = 0; i < k; i++) {
            satisfy += count[i] * ss[i];
        }
        return satisfy;
    }
 
    public double run(int round, ArrayList<double[]> datasource, int len) {
        System.out.println("第" + round + "次运行");
        initCenter(len,datasource);
        classify(datasource);
        while (!calNewCenter(datasource, len)) {
            classify(datasource);
        }
        //datasource.printResult(datasource, k);
        double ss = getSati(datasource, len);
        System.out.println("加权方差：" + ss);
        return ss;
    }
 
    public static void main(String[] args) throws SQLException {
    	
        
    }
}