# Symbolic Execution using SPF and ABC
SPF is a symbolic execution tool for Java built on top of Java pathfinder (http://javapathfinder.sourceforge.net/). On the other hand, ABC (https://vlab.cs.ucsb.edu/ABC/) is automata based string constraint solver and model counter. To run SPF with ABC, all you need is to install ABC and define corresponding variables in the configuration file (explained in later sections) for SPF.

# SPF Installation Guideline
To setup SPF, follow this link :

https://github.com/SymbolicPathFinder/jpf-symbc

# ABC Installation Guideline
To install and run ABC, detailed guidelines have been explained in the following link :

https://github.com/vlab-cs-ucsb/abc

To know about ABC usage with programming languages like C++ and/or Java, follow **Usage** section from the above link.

# Settings for symbolic string and ABC
Check this following directory in SPF. Here, you will find different java example code and corresponding configuration files.

https://github.com/SymbolicPathFinder/jpf-symbc/tree/master/src/examples/strings

* To use symbolic string, you need to set following :
```
symbolic.strings=true
```

* To use ABC, you need to set following :
```
symbolic.string_dp=ABC
```

* To define string length  (for example 0 to 4) and range (for example A to Z ), you need to set following :
```
symbolic.string_range=/[A-Z]{0,4}/
```


If you want to count models for string constraints using ABC, you need to define extra variables in the 
configuration file. Note that, default SPF does not process configuration file variables used for model counting using ABC. 
So, you need to write required code  on java side to read those variables from configuration file.

* To set model counting mode for string constraints : 
```
model_count.mode=abc.string
```

* To set model counting mode for linear arithmetic and integer constraints : 
```
model_count.mode=abc.linear_integer_arithmetic
```

* To set string length bound 4 if your model counting mode is abc.string :
```
model_count.string_length_bound = 4
```

* To set variables for which you want to count models (multiple variables are separated by comma) :
```
model_count.vars = l,h
```

# Examples

**1. Example code and configuration file (Password Checker):**

Code:

```
  public class PasswordCheckWithString {

      private static String password;

      public static boolean verifyPasswordInsecure(final String s) {
          Debug.assume(password.length() <= 4);
          Debug.assume(s.length() <= 4);

          if (s.length() != password.length())
              return false;

          for (int i = 0; i < password.length(); ++i) {
              if (s.charAt(i) != password.charAt(i)) {
                  return false;
              }
          }
          return true;
      }

      public static void main(String[] args) throws InterruptedException {      
          password = Debug.makeSymbolicString(args[2]);
          String input = Debug.makeSymbolicString(args[1]);

          boolean check = verifyPasswordInsecure(input);
          if (check) {
              System.out.println("Password accepted");
          } else {
              System.out.println("Access denied");
          }
      }
  }
```

Configuration:

```
#class
target = fse.PasswordCheckWithString
#main method arguments
target.args = 4, l, h

#required classpath
classpath=${jpf-security}/build/main;${jpf-security}/build/examples 
#required sourcepath
sourcepath=${jpf-security}/src/examples

#jpf listener
listener=sidechannel.abc.TimingSideChannelListener

#to use symbolic string
symbolic.strings=true
#to use abc for string constraints solving
symbolic.string_dp=ABC
#defining string range and length
symbolic.string_range=/[A-Z]{0,4}/
```

**2 . Example code and configuration file using symbolic.method (Bubble Sort):**

Code:

```
import java.util.Random;

public class BubbleSort {
    public void sort(int a[]) {
        int i, j, temp, n = a.length;
        for (i = 0; i < n - 1; ++i) {
            for (j = 0; j < n - 1 - i; ++j) {
                if (a[j] > a[j + 1]) {
                    temp = a[j + 1];
                    a[j + 1] = a[j];
                    a[j] = temp;
                }
            }
        }
    }

    public static void main(String[] args) {
        int length = 4;
        if (args.length > 0) {
            try {
                length = Integer.parseInt(args[0]);
            } catch (Exception e) {}
        }

        Random rand = new Random();
        BubbleSort bs = new BubbleSort();

        int[] arr = new int[length];
        for (int i = 0; i < length; i++) {
            arr[i] = rand.nextInt(200) - 100;
        }

        bs.sort(arr);
    }
}
```

Configuration:

```
#class
target=abccache.BubbleSort
#symbolic method
symbolic.method=abccache.BubbleSort.sort(sym)
#main method arguments
target.args=4

classpath=${jpf-security}/build/examples
sourcepath=${jpf-security}/src/examples

#jpf listener
listener=sidechannel.abc.TimingSideChannelListener

#z3bitvector is used to solve constraints
symbolic.dp=z3bitvector

#to model count on linear arithmeic constraints using ABC
model_count.mode=abc.linear_integer_arithmetic

#turn on symbolic debugging true or false
symbolic.debug = false

#to define maximum and minimum integer
symbolic.min_int=0
symbolic.max_int=127
symbolic.min_long=0
symbolic.max_long=127

#symbolic exution search depth limit
search.depth_limit = 30

```

# Running SPF
Considering SPF and ABC is properly installed and having idea about required changes to make in configuration file to run SPF with ABC, next task is to run SPF. You need to do the following

```
cd path/to/jpf-symbc
jpf src/examples/strings/file-to-run.jpf
```
