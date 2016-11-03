package vlab.cs.ucsb.edu;

import java.math.BigInteger;
import java.util.Map;

/**
 * ABC Java Interface
 * 
 * set JVM argument -Djava.library.path=/usr/local/lib or set env. variable
 * LD_LIBRARY_PATH to make sure 'libabc' is available to JVM
 * 
 * @author baki
 *
 */
public class DriverProxy {
	public enum Option {
		USE_SIGNED_INTEGERS(0), 			// default option
		USE_UNSIGNED_INTEGERS(1), 
		USE_MULTITRACK_AUTO(2), 			// default option
		USE_SINGLETRACK_AUTO(3), 
		ENABLE_EQUIVALENCE_CLASSES(4),		// default option
		DISABLE_EQUIVALENCE_CLASSES(5), 
		ENABLE_DEPENDENCY_ANALYSIS(6), 		// default option
		DISABLE_DEPENDENCY_ANALYSIS(7), 
		ENABLE_IMPLICATIONS(8), 			// default option
		DISABLE_IMPLICATIONS(9), 
		ENABLE_SORTING_HEURISTICS(10), 		// default option
		DISABLE_SORTING_HEURISTICS(11), 
		OUTPUT_PATH(12), 					// not actively used through Java
		SCRIPT_PATH(13);					// not actively used

		private final int value;

		private Option(int value) {
			this.value = value;
		}

		public int getValue() {
			return this.value;
		}
	}

	private long driverPointer;
	
	static {
		System.loadLibrary("abc");
	}

	public DriverProxy() {
		initABC(0);
	}

	public DriverProxy(final int logLevel) {
		initABC(logLevel);
	}
	
	public void setOption(final Option option) {
		setOption(option.getValue());
	}

	public void setOption(final Option option, final String value) {
		setOption(option.getValue(), value);
	}

	private native void initABC(final int logFlag);

	private native void setOption(final int option);

	private native void setOption(final int option, final String value);

	public native boolean isSatisfiable(final String constraint);

	public native BigInteger countVariable(final String varName, final long bound);
	
	public native BigInteger countInts(final long bound);
	
	public native BigInteger countStrs(final long bound);
	
	public native BigInteger count(final long intBound, final long strBound);
	
	public native String getModelCounterForVariable(final String varName);
	
	public native String getModelCounterForInts();
	
	public native String getModelCounterForStrs();
	
	public native String getModelCounter();

	public native BigInteger countVariable(final String varName, final long bound, final String binaryModelCounterString);
	
	public native BigInteger countInts(final long bound, final String binaryModelCounterString);
	
	public native BigInteger countStrs(final long bound, final String binaryModelCounterString);

	public native BigInteger count(final long intBound, final long strBound, final String binaryModelCounterString);

	public native void printResultAutomaton();

	public native void printResultAutomaton(String filePath);

	public native Map<String, String> getSatisfyingExamples();

	public native void reset();

	public native void dispose();
}
