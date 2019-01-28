import java.math.BigInteger;
import java.util.Map;
import java.util.Map.Entry;

import vlab.cs.ucsb.edu.DriverProxy;
import vlab.cs.ucsb.edu.DriverProxy.Option;

public class ExampleUsage {

  public static void main(String[] args) {

    DriverProxy abcDriver = new DriverProxy();
    
    
    String core_constraint = "(set-logic QF_S)\n"
        + "(declare-fun h () String)\n"
        + "(declare-fun l () String)\n"
        + "(assert (in h /[A-Z]{4,}/))\n"
        + "(assert (in l /[A-Z]{4,}/))\n"
        + "(assert (= (charAt h 0) (charAt l 0)))\n"
        + "(check-sat)";
    // solve initial constraint, 
    
    boolean result = abcDriver.isSatisfiable2(core_constraint, true);
    System.out.println("----------DONE CORE-----------");
    // get id of core constraint
    String core_constraint_id = abcDriver.getCurrentID();

    // from core constraint, we have two branches we want to build off of
    String branch1 = core_constraint + "(assert (< l h))";
    String branch2 = core_constraint + "(assert (> l h))";


    // isSatisfiable2 assumes incremental mode; takes two params: constraint, and branch
    // if branch = true, then ABC will save the current ID, clone it, give the clone a new ID,
    //                   and continue from there in incremental mode
    // if branch = false, then ABC will use the state associated with the current ID and
    //                   continue from there in incremental mode; e.g., the current state is
    //                   taken as the "initial" state for the next solve, and is modified from thereon
    result = abcDriver.isSatisfiable2(branch1, true);
    // since branch=true, we gotta get the ID if we want to come back to this state
    String branch1_id = abcDriver.getCurrentID();


    // lets get a random example, bounded, for h with bound of 5
    Map<String, String> results = abcDriver.getSatisfyingExamplesRandomBounded(5);
    for (Entry<String, String> var_result : results.entrySet()) {
      System.out.println(var_result.getKey() + " : \"" + var_result.getValue() + "\"");
    }
    System.out.println("----------DONE BRANCH1------------");


    // lets go back and solve for branch 2 now
    // load core id
    abcDriver.loadID(core_constraint_id);
    // tell ABC to branch and solve for branch2 constraint
    result = abcDriver.isSatisfiable2(branch2, true);
    // lets get a random example, bounded, for h with bound of 5
    results = abcDriver.getSatisfyingExamplesRandomBounded(5);
    for (Entry<String, String> var_result : results.entrySet()) {
      System.out.println(var_result.getKey() + " : \"" + var_result.getValue() + "\"");
    }
    System.out.println("-----------DONE BRANCH2-----------");


    System.out.println("Before destroy");
    String id_to_delete = abcDriver.getCurrentID();
    abcDriver.destroyID(id_to_delete);
    System.out.println("After destroy");



    // lets go back to branch1
    //abcDriver.loadID(core_constraint_id);
    // lets go incremental, but make branch=false; this will take branch1_id's state
    // and continue on with it, without making a copy
    String branch1_constraint2 = branch2 + "(assert (= (charAt h 1) \"Z\"))";
    result = abcDriver.isSatisfiable2(branch1_constraint2,true);

    results = abcDriver.getSatisfyingExamplesRandomBounded(5);
    for (Entry<String, String> var_result : results.entrySet()) {
      System.out.println(var_result.getKey() + " : \"" + var_result.getValue() + "\"");
      String mutated_model = abcDriver.mutateModel(var_result.getKey(),var_result.getValue());
      System.out.println(var_result.getKey() + "(mutated) : \"" + mutated_model + "\"");
    }
    System.out.println("-----------END-----------");
    
    
    abcDriver.dispose(); // release resources
  }
}
