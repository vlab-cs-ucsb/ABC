import java.math.BigInteger;
import java.util.Map;
import java.util.Map.Entry;

import vlab.cs.ucsb.edu.DriverProxy;
import vlab.cs.ucsb.edu.DriverProxy.Option;

public class ExampleUsage {

  public static void main(String[] args) {

    DriverProxy abcDriver = new DriverProxy();
    
    abcDriver.setOption(Option.ENABLE_IMPLICATIONS);
    abcDriver.setOption(Option.USE_SIGNED_INTEGERS);
    
    String constraint = "(set-logic QF_S)\n"
        + "(declare-fun var_abc () String)\n"
        + "(assert (= var_abc (concat \"a\" \"b\")))\n"
        + "(check-sat)";
    
    boolean result = abcDriver.isSatisfiable(constraint);
    
    if (result) {
      System.out.println("Satisfiable");
      long bound = 15;
      String func = abcDriver.getModelCounterForVariable("var_abc");
      System.out.println("func: " + func);
      BigInteger count = abcDriver.countVariable("adf",bound);
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
//    String func = abcDriver.getModelCounterForInts();
//    System.out.println("func: " + func);
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
