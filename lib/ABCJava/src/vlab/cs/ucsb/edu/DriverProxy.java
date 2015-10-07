package vlab.cs.ucsb.edu;

import java.util.Map;

/**
 * ABC Java Interface
 * 
 * set JVM argument -Djava.library.path=/usr/local/lib or
 * set env. variable LD_LIBRARY_PATH to 
 * make sure 'libabc' is available to JVM
 * @author baki
 *
 * TODO add more flexibility to constraint construction
 * TODO check for JVM (JNI) thread issues
 */
public class DriverProxy {
  
  private long driverPointer;
  
  static {
    System.loadLibrary("abc");
  }
  
  public DriverProxy() {
    initABC();
  }
  
  private native void initABC();
  public native boolean isSatisfiable(String constraint);
  public native void printResultAutomaton();
  public native void printResultAutomaton(String filePath);
  public native Map<String, String> getSatisfyingExamples();
  public native void reset();
  public native void dispose();
}
