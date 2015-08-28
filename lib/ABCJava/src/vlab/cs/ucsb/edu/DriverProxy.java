package vlab.cs.ucsb.edu;

/**
 * ABC Java Interface
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
  public native void reset();
  public native void dispose();
}
