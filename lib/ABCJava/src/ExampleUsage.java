import java.math.BigDecimal;
import java.util.Map;
import java.util.Map.Entry;

import vlab.cs.ucsb.edu.DriverProxy;
import vlab.cs.ucsb.edu.DriverProxy.Option;

public class ExampleUsage {

  public static void main(String[] args) {

    DriverProxy abcDriver = new DriverProxy();
    abcDriver.setOption(Option.OUTPUT_PATH, "./");
    abcDriver.setOption(Option.SCRIPT_PATH, "/home/baki/Projects/ABC/lib/mathematica");
    abcDriver.setOption(Option.MODEL_COUNTER_ENABLED, true);
    abcDriver.setOption(Option.LIA_ENGINE_ENABLED, true);
    abcDriver.setOption(Option.LIA_NATURAL_NUMBERS_ONLY, true);
    
    String constraint = "(set-logic QF_S)\n"
        + "(declare-fun var_abc () String)\n"
        + "(assert (= var_abc (concat \"a\" \"b\")))\n"
        + "(check-sat)";
    
    boolean result = abcDriver.isSatisfiable(constraint);
    
    if (result) {
      System.out.println("Satisfiable");
      int bound = 15;
      BigDecimal count = abcDriver.count("var_abc", bound);
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
      double bound = 5;
      BigDecimal count = abcDriver.symbolicCount(bound);
      if (count != null) {
        System.out.println("Number of solutions within bound " + bound + " is " + count.toString());
      } else {
        System.out.println("An error occured during counting, please contact vlab@cs.ucsb.edu");
      }
      
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
