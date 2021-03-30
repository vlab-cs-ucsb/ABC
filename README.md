ABC
============
The Automata Based Counter ([ABC](https://vlab.cs.ucsb.edu/ABC/)) is a **string and numeric constraint** solver and
**model counter**. ABC provides solutions to systems of string and numeric constraints in the form of a deterministic
finite automaton. In addition ABC produces symbolic representation of the number of strings and integers within a length
bound, k, that satisfy a set of constraints. ABC can also output the number of satisfying solutions given a bound.

Publications 
============

ABC algorithmic details:
------------
- **ASE'19**, [Subformula Caching for Model Counting and Quantitative Program Analysis](https://vlab.cs.ucsb.edu/papers/ase2019_counting_caching_cr.pdf). William Eiers, Seemanta Saha, Tegan Brennan, Tevfik Bultan.

- **FSE'18**, [Parameterized Model Counting for String and Numeric Constraints](https://dl.acm.org/citation.cfm?doid=3236024.3236064).  Abdulbaki Aydin, William Eiers, Lucas Bang, Tegan Brennan, Miroslav Gavrilov, Tevfik Bultan, Fang Yu.

- **CAV'15**, [Automata-based model counting for string constraints](http://www.cs.ucsb.edu/~baki/publications/cav15.pdf). Abdulbaki Aydin, Lucas Bang, and Tevfik Bultan. <br>
[Download experimental data and results.](https://vlab.cs.ucsb.edu/ABC/)

ABC use cases:
------------

- **JPF'19**, [Incremental Attack Synthesis](https://vlab.cs.ucsb.edu/papers/jpf2019.pdf). Seemanta Saha, William Eiers, Ismet Burak Kadron, Lucas Bang, Tevfik Bultan. 

- **JPF'18**, [Attack Synthesis for Strings using Meta-Heuristics](https://vlab.cs.ucsb.edu/papers/jpf2018.pdf). Seemanta Saha, Ismet Burak Kadron, William Eiers, Lucas Bang, Tevfik Bultan.

- **FSE'16**, [String Analysis for Side Channels with Segmented Oracles](http://www.cs.ucsb.edu/~baki/publications/fse16.pdf). Lucas Bang, Abdulbaki Aydin, Quoc-Sang Phan, Corina S. Pasareanu, and Tevfik Bultan. 

Download
============
Latest version of ABC is available on GitHub: 
https://github.com/vlab-cs-ucsb/ABC

A Docker image of ABC (pre-built and ready to go!) is also available through DockerHub: vlabucsb/abc:ubuntu
(No java)

Setup
============
ABC can be built for Linux and MacOS. For detailed build instructions, see [INSTALL.md](https://github.com/vlab-cs-ucsb/ABC/blob/master/INSTALL.md)

Usage
============

#### C++
You can link to dynamic library generated in your program. An example executable for abc is generated for you and install in your system. You can run abc executable at your home directory as:
  
    $ abc -i  <input_file_path>
    $ abc --help #lists available command line options

E.g.,

    $ abc -i <abc source folder>/test/fixtures/solver/ConstraintSolver/test_visitBegins_01.smt2

For an example of model counting a string with bound <= 5:

    $ abc -i <abc source folder>/test/fixtures/solver/ConstraintSolver/test_visitBegins_01.smt2 -v 0 -bs 5

where -v 0 disables debugging output, and -bs 5 means count solutions with bound <= 5

If there are more than one string variables, you can specify which one you want to model count with the argument: --count-variable <VARIABLE_NAME>
  
You can take a look at *__&lt;abc source folder&gt;/src/main.cpp__* to see how *__abc__* is used in a C++ program as a shared library. 
  
(More documentation on ABC input language and format will be provided, please see *__&lt;abc-source-folder&gt;/test/fixtures__* folder for examples)
  
#### JAVA

You have to compile *__ABC__* with your *__JAVA_HOME__* path is set to a valid java path. Once you set your *__JAVA_HOME__* path, you need to install/re-install *__ABC__* on your system. 
  
You need to set Java VM argument __java.library.path__ to path where your shared libraries are install, or alternatively you can set __LD_LIBRARY_PATH__ environment variable to that path.

You can use *__&lt;abc-source-folder&gt;/lib/ABCJava__* as an example Java program that calls __abc__.

In your Java project all you have to do is to include the contents of *__&lt;abc-source-folder&gt;/lib/ABCJava/src/__*. *vlab.cs.ucsb.edu.DriverProxy.java* class is the class that makes abc calls.
  
#### SPF (Symbolic Execution)

https://github.com/vlab-cs-ucsb/ABC/blob/master/spf-with-abc-readme.md
  
ABC Language Specification
==========================

ABC conforms to the [SMT2Lib specification](http://smtlib.cs.uiowa.edu/) for string and linear integer arithmetic theories.
