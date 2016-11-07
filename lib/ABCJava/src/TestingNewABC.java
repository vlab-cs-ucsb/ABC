import java.math.BigInteger;
import vlab.cs.ucsb.edu.DriverProxy;

public class TestingNewABC {

	private static String query1 = 
			  "(declare-fun x () String) \n"
			+ "(declare-fun y () String) \n"
			+ "(declare-fun z () String) \n"
			+ "(assert (= z (concat x y))) \n"
			+ "(assert (= x \"Sudden\")) \n"
			+ "(assert (= y \"Glamour\")) \n"
			+ "(check-sat)";

	private static String query2 = 
			  "(declare-fun x () String) \n"
			+ "(declare-fun y () String) \n"
			+ "(declare-fun z () String) \n"
			+ "(assert (= z (concat x y))) \n"
			+ "(assert (= x \"Sudden\")) \n"
			+ "(assert (in y /[A-Z][a-z]+/)) \n"
			+ "(check-sat)";

	private static String query3 = 
			  "(declare-fun x () String) \n"
			+ "(declare-fun y () String) \n"
			+ "(declare-fun z () String) \n"
			+ "(assert (= z (concat x y))) \n"
			+ "(check-sat)";

	private static String query4 = 
			  "(declare-fun z () String) \n"
			+ "(assert (= z z)) \n"
			+ "(check-sat)";
	
	private static String query5 = // WORKS
			  "(declare-fun z () String)\n"
			  + "(assert (= (len z) 0))\n"
			  + "(check-sat)";

	private static String query6 = // DOESN'T WORK
			  "(declare-fun z () String)\n"
			  + "(declare-fun x () String)\n"
			  + "(assert (= z x))\n"
			  + "(assert (= (len x) 0))\n"
			  + "(check-sat)";
	
	private static long BOUND = 15;
	

	public static void testCount() {

		System.out.println("Creating abc solver");
		DriverProxy abc = new DriverProxy();
		
		String query = query6;
		long bound = BOUND;
		
		System.out.println("Query:\n" + query + "\n");

		Boolean result = abc.isSatisfiable(query);
		if(result) {
			BigInteger n = abc.countVariable("z", bound);
			System.out.println("Count: " + n.toString());
		} else {
			System.out.println("UNSAT!");			
		}
		
		System.out.println("Disposing abc solver");
		abc.dispose();
		
	}

	public static void testCountingFunction() {

		byte[] func = null;
		
		System.out.println("Creating first abc solver");
		DriverProxy abc = new DriverProxy();

		//abc.setOption(Option.ENABLE_IMPLICATIONS);
		
		String query = query6;
		long bound = BOUND;
		
		System.out.println("Query:\n" + query + "\n");

		Boolean result = abc.isSatisfiable(query);
		if(result) {
			func = abc.getModelCounterForVariable("z");
			System.out.println("Counting function: " + func.toString());
			System.out.println("Counting function size: " + func.length);
		} else {
			System.out.println("UNSAT!");
			return;
		}
		
		System.out.println("Going to dispose of first abc solver");
		abc.dispose();
		System.out.println("Done disposing of first abc solver");
		

		System.out.println("\nCreating another abc solver");
		abc = new DriverProxy();

		System.out.println("Counting using the previously obtained function...");
		System.out.println("Bound size: " + bound);
		BigInteger n = abc.countVariable("z", bound, func);
		System.out.println("Count: " + n.toString());

		System.out.println("Going to dispose of second abc solver");
		abc.dispose();
		System.out.println("Done disposing of second abc solver");
		
	}
	
	
	public static void main(String[] args) {
		testCount();
		testCountingFunction();
	}

}
