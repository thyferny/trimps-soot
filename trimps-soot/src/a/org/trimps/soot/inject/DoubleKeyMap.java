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
     * 由键2取得键1 
     *  
     * @param k2 
     *            键2 
     * @return 返回对应的键1 
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
     * 由键1 取得键2 
     *  
     * @param k1 
     *            键1 
     * @return 返回对应的键2 
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