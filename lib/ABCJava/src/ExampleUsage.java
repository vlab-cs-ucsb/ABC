import vlab.cs.ucsb.edu.DriverProxy;

public class ExampleUsage {

  public static void main(String[] args) {
    // TODO Auto-generated method stub
    DriverProxy abcDriver = new DriverProxy();
    
    String constraint = "(set-logic QF_S)\n"
        + "(declare-fun var_abc () String)\n"
        + "(assert (= var_abc (concat \"a\" \"b\")))\n"
        + "(check-sat)";
    
    boolean result = abcDriver.isSatisfiable(constraint);
    if (result) {
      System.out.println("Satisfiable");
      abcDriver.printResultAutomaton();
    } else {
      System.out.println("Unsatisfiable");
    }
    
    abcDriver.dispose();
  }
}
