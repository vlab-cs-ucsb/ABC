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
        + "(assert (not (= var_abc \"abc\")))\n"
        + "(check-sat)";
    
    boolean result = abcDriver.isSatisfiable(constraint);
    
    if (result) {
      System.out.println("Satisfiable");
      long bound = 2;
      BigInteger count = abcDriver.countVariable("var_abc",bound);
      byte[] func = abcDriver.getModelCounterForVariable("var_abc");
      System.out.println("len: " + func.length);
      System.out.println("func: " + func);
      if (count != null) {
        System.out.println("Number of solutions within bound: " + bound + " is " + count.toString());
      } else {
        System.out.println("An error occured during counting, please contact vlab@cs.ucsb.edu");
      }
      
      BigInteger count2 = abcDriver.countVariable("var_abc", bound, func);
      
      System.out.println("cache count: " + count2);
      
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
