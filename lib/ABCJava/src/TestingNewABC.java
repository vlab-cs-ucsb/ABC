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
	
	private static long BOUND = 15;
	

	public static void testCount() {

		System.out.println("Creating abc solver");
		DriverProxy abc = new DriverProxy();
		
		String query = query2;
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

		System.out.println("Creating abc solver");
		DriverProxy abc = new DriverProxy();
		
		String query = query2;
		long bound = BOUND;
		
		System.out.println("Query:\n" + query + "\n");

		Boolean result = abc.isSatisfiable(query);
		if(result) {
			byte[] func = abc.getModelCounterForVariable("z");
			System.out.println("Counting function: " + func.toString());
			System.out.println("Counting function size: " + func.length);
			
			BigInteger n = abc.countVariable("z", bound, func);
			System.out.println("Count: " + n.toString());
		} else {
			System.out.println("UNSAT!");			
		}
		
		System.out.println("Disposing abc solver");
		abc.dispose();
		
	}
	
	
	public static void main(String[] args) {
		testCount();
		testCountingFunction();
	}

}
