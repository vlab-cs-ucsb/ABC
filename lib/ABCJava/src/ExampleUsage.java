import java.math.BigInteger;
import java.util.Map;
import java.util.Map.Entry;

import vlab.cs.ucsb.edu.DriverProxy;

public class ExampleUsage {

  public static void main(String[] args) {

    DriverProxy abcDriver = new DriverProxy();
    
    String constraint = "(set-logic QF_S)\n"
        + "(declare-fun var_abc () String)\n"
        + "(assert (= var_abc (concat \"a\" \"b\")))\n"
        + "(check-sat)";
    
    boolean result = abcDriver.isSatisfiable(constraint);
    
    if (result) {
      System.out.println("Satisfiable");
      long bound = 15;
      BigInteger count = abcDriver.countVariable("var_abc", bound);
      if (count != null) {
        System.out.println("Number of solutions within bound: " + bound + " is " + count.toString());
      } else {
        System.out.println("An error occured during counting, please contact vlab@cs.ucsb.edu");
      }
      
//      abcDriver.printResultAutomaton();
      
      Map<String, String> results = abcDriver.getSatisfyingExamples();
      for (Entry<String, String> var_result : results.entrySet()) {
        System.out.println(var_result.getKey() + " : \"" + var_result.getValue() + "\"");
      }
    } else {
      System.out.println("Unsatisfiable");
    }
    
    constraint = "(declare-fun x () Int)\n"
            + "(declare-fun y () Int)\n"
            + "(assert (= x (* 2 y)))\n"
            + "(assert (> x 0))\n"
            + "(check-sat)"; 

    result = abcDriver.isSatisfiable(constraint);
    
    if (result) {
      System.out.println("Satisfiable");
          
      Map<String, String> results = abcDriver.getSatisfyingExamples();
      for (Entry<String, String> var_result : results.entrySet()) {
        System.out.println(var_result.getKey() + " : \"" + var_result.getValue() + "\"");
      }
    } else {
      System.out.println("Unsatisfiable");
    }
    
    abcDriver.dispose(); // release resources
  }
}
