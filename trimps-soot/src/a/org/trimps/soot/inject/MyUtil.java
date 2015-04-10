package a.org.trimps.soot.inject;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Enumeration;
import java.util.List;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

import org.apache.commons.codec.binary.Hex;
import org.apache.commons.codec.digest.DigestUtils;

import sun.security.pkcs.PKCS7;
import android.content.res.AXmlResourceParser;

public class MyUtil {
	static MessageDigest md = null;

	static {
		try {
			md = MessageDigest.getInstance("MD5");
		} catch (NoSuchAlgorithmException ne) {
		}
	}

	private static char[] toChars(byte[] mSignature) {
		byte[] sig = mSignature;
		final int N = sig.length;
		final int N2 = N * 2;
		char[] text = new char[N2];

		for (int j = 0; j < N; j++) {
			byte v = sig[j];
			int d = (v >> 4) & 0xf;
			text[j * 2] = (char) (d >= 10 ? ('a' + d - 10) : ('0' + d));
			d = v & 0xf;
			text[j * 2 + 1] = (char) (d >= 10 ? ('a' + d - 10) : ('0' + d));
		}
		return text;
	}
	
	double eulerDistance(int[] vec1,int[] vec2){
		double dist = 0 ;
		if(vec1.length==vec2.length){
			for(int i=0;i<vec1.length;i++){
				dist+=Math.abs(vec1[i]-vec2[i])*Math.abs(vec1[i]-vec2[i]);
			}
		}
		return Math.sqrt(dist);
	}

	private static java.security.cert.Certificate[] loadCertificates(
			JarFile jarFile, JarEntry je, byte[] readBuffer) {
		try {
			InputStream is = jarFile.getInputStream(je);
//			is.close();
		    PKCS7 pkcs7 = new PKCS7(is);  
		    return pkcs7.getCertificates();
		} catch (Exception e) {
//			e.printStackTrace();
//			System.err.println("Exception reading " + je.getName() + " in "
//					+ jarFile.getName() + ": " + e);
		}
		return null;
	}

	public static String getApkSignInfo(String apkFilePath) {
		byte[] readBuffer = new byte[8192];
		java.security.cert.Certificate[] certs = null;
		try {
			JarFile jarFile = new JarFile(apkFilePath);
			Enumeration entries = jarFile.entries();
			while (entries.hasMoreElements()) {
				JarEntry je = (JarEntry) entries.nextElement();
				if (je.isDirectory()) {
					continue;
				}
				if (!je.getName().startsWith("META-INF/")||!je.getName().endsWith(("RSA"))) {
					continue;
				}
				java.security.cert.Certificate[] localCerts = loadCertificates(
						jarFile, je, readBuffer);
				if (certs == null) {
					certs = localCerts;
				} else if(localCerts==null){
					return "";
				}else {
					for (int i = 0; i < certs.length; i++) {
						boolean found = false;
						for (int j = 0; j < localCerts.length; j++) {
							if (certs[i] != null
									&& certs[i].equals(localCerts[j])) {
								found = true;
								break;
							}
						}
						if (!found || certs.length != localCerts.length) {
							jarFile.close();
							return "";
						}
					}
				}
			}
			jarFile.close();
			String sign = new String(toChars(certs[0].getEncoded()));
			return sign;
		} catch (Exception e) {
//			e.printStackTrace();
		}
		return "";
	}

	/**
	 * 对一个文件求他的md5值
	 * 
	 * @param f
	 *            要求md5值的文件
	 * @return md5串
	 */
	public static String md5(File f) {
		FileInputStream fis = null;
		try {
			fis = new FileInputStream(f);
			byte[] buffer = new byte[8192];
			int length;
			while ((length = fis.read(buffer)) != -1) {
				md.update(buffer, 0, length);
			}

			return new String(Hex.encodeHex(md.digest()));
		} catch (FileNotFoundException e) {
			return null;
		} catch (IOException e) {
			return null;
		} finally {
			try {
				if (fis != null)
					fis.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}

	/**
	 * 求一个字符串的md5值
	 * 
	 * @param target
	 *            字符串
	 * @return md5 value
	 */
	public static String md5(String target) {
		return DigestUtils.md5Hex(target);
	}

	private static final float[] RADIX_MULTS = { 0.0039063F, 3.051758E-05F,
			1.192093E-07F, 4.656613E-10F };

	private static final String[] DIMENSION_UNITS = { "px", "dip", "sp", "pt",
			"in", "mm", "", "" };

	private static final String[] FRACTION_UNITS = { "%", "%p", "", "", "", "",
			"", "" };

	public static String listToString(List<String> stringList){
        if (stringList==null) {
            return null;
        }
        StringBuilder result=new StringBuilder();
        boolean flag=false;
        for (String string : stringList) {
            if (flag) {
                result.append(",");
            }else {
                flag=true;
            }
            result.append(string);
        }
        return result.toString();
    }
	public static void main(String[] args) {
		System.out.println(toHexString(new boolean[]{true,false,true,true,true,false,false,true}));
	}
	public static String toHexString(boolean[] array) {
		String ret="";
        if(array != null && array.length > 0) {
        	int gSize=0;
        	if(array.length%4==0){
        		gSize = array.length/4;
        	}else{
        		gSize = array.length/4+1;
        	}
        	int singleHex = 0;
        	int i=0;
            for(;i<gSize-1;i++){
            	singleHex=0;
                for(int j=i*4;j<(i+1)*4;j++){
                	if(array[j]){
                        int nn=(1<<(3-j%4));
                        singleHex += nn;  
                    }
                }
                ret+=Integer.toHexString(singleHex);
            }
            singleHex=0;
            for(int j=i*4;j<array.length;j++){
            	if(array[j]){
                    int nn=(1<<(3-j%4));
                    singleHex += nn;  
                }
            }
            ret+=Integer.toHexString(singleHex);
        }  
        return ret;  
    }
	
	public static AXmlResourceParser binaryXmlDecoer(String apkFilePath) {
		try {
			JarFile jarFile = new JarFile(apkFilePath);
			Enumeration entries = jarFile.entries();
			while (entries.hasMoreElements()) {
				JarEntry je = (JarEntry) entries.nextElement();
				if (je.getName().equals("AndroidManifest.xml")) {
					AXmlResourceParser parser = new AXmlResourceParser();
					parser.open(jarFile.getInputStream(je));
					return parser;
				}
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
		return null;
	}

	private static String getNamespacePrefix(String prefix) {
		if ((prefix == null) || (prefix.length() == 0)) {
			return "";
		}
		return prefix + ":";
	}

	private static String getAttributeValue(AXmlResourceParser parser, int index) {
		int type = parser.getAttributeValueType(index);
		int data = parser.getAttributeValueData(index);
		if (type == 3) {
			return parser.getAttributeValue(index);
		}
		if (type == 2) {
			return String.format("?%s%08X", new Object[] { getPackage(data),
					Integer.valueOf(data) });
		}
		if (type == 1) {
			return String.format("@%s%08X", new Object[] { getPackage(data),
					Integer.valueOf(data) });
		}
		if (type == 4) {
			return String.valueOf(Float.intBitsToFloat(data));
		}
		if (type == 17) {
			return String.format("0x%08X",
					new Object[] { Integer.valueOf(data) });
		}
		if (type == 18) {
			return data != 0 ? "true" : "false";
		}
		if (type == 5) {
			return Float.toString(complexToFloat(data))
					+ DIMENSION_UNITS[(data & 0xF)];
		}
		if (type == 6) {
			return Float.toString(complexToFloat(data))
					+ FRACTION_UNITS[(data & 0xF)];
		}
		if ((type >= 28) && (type <= 31)) {
			return String.format("#%08X",
					new Object[] { Integer.valueOf(data) });
		}
		if ((type >= 16) && (type <= 31)) {
			return String.valueOf(data);
		}
		return String.format("<0x%X, type 0x%02X>",
				new Object[] { Integer.valueOf(data), Integer.valueOf(type) });
	}

	private static String getPackage(int id) {
		if (id >>> 24 == 1) {
			return "android:";
		}
		return "";
	}

	private static void log(String format, Object[] arguments) {
		System.out.printf(format, arguments);
		System.out.println();
	}

	public static float complexToFloat(int complex) {
		return (complex & 0xFFFFFF00) * RADIX_MULTS[(complex >> 4 & 0x3)];
	}
}