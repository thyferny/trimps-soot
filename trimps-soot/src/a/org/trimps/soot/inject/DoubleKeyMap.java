package a.org.trimps.soot.inject;

import java.util.ArrayList;

public class DoubleKeyMap<K1, K2> {  
  
    private ArrayList<K1> key1s;  
    private ArrayList<K2> key2s;  
  
    public DoubleKeyMap() {  
        key1s = new ArrayList<K1>();  
        key2s = new ArrayList<K2>();  
    }  
  
    public ArrayList<K1> key1(){
    	return key1s;
    }
    public ArrayList<K2> key2(){
    	return key2s;
    }
    
    public DoubleKeyMap<K1, K2> add(K1 k1, K2 k2) {  
        if (k1 == null || k2 == null) {  
            throw new IllegalArgumentException(  
                    "both the parameters could not be null.");  
        }  
        if (key1s.contains(k1)) {  
            throw new IllegalArgumentException("the key1 has been put");  
        }  
  
        if (key2s.contains(k2)) {  
            throw new IllegalArgumentException("the key2 has been put");  
        }  
        key1s.add(k1);  
        key2s.add(k2);  
        return this;  
    }  
  
    /** 
     * �ɼ�2ȡ�ü�1 
     *  
     * @param k2 
     *            ��2 
     * @return ���ض�Ӧ�ļ�1 
     */  
    public K1 getKey1(K2 k2) {
    	int index = key2s.indexOf(k2);
    	if(index==-1){
    		return null;
    	}else{
    		return key1s.get(index);
    	}
    }  
  
    /** 
     * �ɼ�1 ȡ�ü�2 
     *  
     * @param k1 
     *            ��1 
     * @return ���ض�Ӧ�ļ�2 
     */  
    public K2 getKey2(K1 k1) {  
        int index = key1s.indexOf(k1);
    	if(index==-1){
    		return null;
    	}else{
    		return key2s.get(index);
    	}
    }  
}  