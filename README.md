ABC
============
The Automata Based Counter ([ABC](https://vlab.cs.ucsb.edu/ABC/)) is a **string and numeric constriant** solver and
**model counter**. ABC provides solutions to systems of string and numeric constraints in the form of a deterministic
finite automaton. In addition ABC produces symbolic representation of the number of strings and integers within a length
bound, k, that satisfy a set of constraints. ABC can also output the number of satisfying solutions given a bound.

Publications
============
###ABC algorithmic details:
- A new publication is coming with improvements over CAV'15 version of ABC.

<!-- - (in submission), [Parameterized Model Counting for String and Numeric Constraints](). Abdulbaki Aydin, Lucas Bang, William Eiers, Tegan Brennan, Miroslav Gavrilov, Tevfik Bultan, and Fang Yu. <br>
[Download experimental data and results.](https://vlab.cs.ucsb.edu/ABC/experimental_data.tar) -->
- **CAV'15**, [Automata-based model counting for string constraints](http://www.cs.ucsb.edu/~baki/publications/cav15.pdf). Abdulbaki Aydin, Lucas Bang, and Tevfik Bultan. <br>
[Download experimental data and results.](https://vlab.cs.ucsb.edu/ABC/)

###ABC use cases:
<!-- - (in submission) , [ISSTAC: Integrated Symbolic Execution for Space-Time Analysis of Code](). Daniel Balasubramanian, Kasper Luckow, Corina Pasareanu, Abdulbaki Aydin, Lucas Bang, Tevfik Bultan, Miroslav Gavrilov, Temesghen Kahsai, Rody Kersten, Dmitriy Kostyuchenko, Quoc-Sang Phan, Zhenkai Zhang and Gabor Karsai. -->
- **FSE'16** [String Analysis for Side Channels with Segmented Oracles](http://www.cs.ucsb.edu/~baki/publications/fse16.pdf). Lucas Bang, Abdulbaki Aydin, Quoc-Sang Phan, Corina S. Pasareanu, and Tevfik Bultan.

Setup
============
ABC is a C++ executable and a C++ shared library with JNI interfaces. You can
use it as a static or dynamic lib or you can run it from command line.

###Download

```
$ cd <your home directory or a preferred directory>
$ git clone --recursive git@github.com:vlab-cs-ucsb/ABC.git ABC # or use https://github.com/vlab-cs-ucsb/ABC.git
```
ABC testing depends on [googletest and googlemock](https://github.com/google/googletest) as subprojects. It is important to clone with ``--recursive`` option.

###Easy(Automated) Setup
  - [ABC](https://vlab.cs.ucsb.edu/ABC/). Clone ABC source and run build script. It automatically tries to install required system packages and dependent projects; [Glog](https://github.com/google/glog) and [Mona](http://www.brics.dk/mona/). After installing dependencies, it installs ABC. If script does not work please try step-by-step guide or contact us. (That script is tested with Linux machines. You can still use build script in other posix systems if you resolve system dependencies manually.)

  ```
  $ cd ABC/build
  $ ./install-build-deps.py
  ```

###Step-by-Step(Semi-automated) Setup
####System Dependencies
  - C++ compiler with C++14 support. Latest ABC compilation is tested with g++ 5.4.0 on Ubuntu 16.04.
  - [Git](https://git-scm.com/)

  ```
    $ sudo apt install git
  ```
  - ABC is an autotools project, you need to setup autotools in your system. Please make sure you have installed all the tools below.

  ```
    $ sudo apt install build-essential autoconf automake libtool intltool
  ```
  - Lex and Yacc. ABC is tested with [Flex 2.6.0](https://www.gnu.org/software/flex/flex.html) and [Bison 3.0.4](https://www.gnu.org/software/bison/).

  ```
    $ sudo apt install flex bison
  ```

  - Python (optional). A short installation script is written in pyhton.

  ```
    $ sudo apt install python
  ```

####Project Dependencies
  - [Glog](https://github.com/google/glog) logging library for C++. It is an autotools project.
  Please follow the instructions in their website if the below shortcut doesn't work for you. Don't forget to apply patch
  as below:

  ```
  $ cd <your home directory or a preferred directory>
  $ git clone https://github.com/google/glog.git
  $ cd glog
  $ git apply <ABC_ROOT_DIR>/external/glog/glog_abc_autotools.patch
  $ libtoolize && aclocal && automake --gnu --add-missing && autoreconf -ivf
  $ ./configure
  $ make all
  $ sudo make install
  $ sudo ldconfig

  ```
  You should have glog libraries installed at */usr/local/lib* and headers installed at */usr/local/include/glog/* after running above commands.

  - [Mona](http://www.brics.dk/mona/) is used for symbolic representation of automata. Don't forget to apply patch as below:

  ```sh
    $ cd <your home directory or a preferred directory>
    $ git clone https://github.com/cs-au-dk/MONA.git
    $ cd MONA
    $ git apply <ABC_ROOT_DIR>/external/mona/mona_abc.patch
    $ libtoolize && aclocal && automake --gnu --add-missing && autoreconf -ivf
    $ ./configure
    $ make all
    $ sudo make install
    $ sudo ldconfig

  ```
  You should have mona libraries installed at */usr/local/lib* and headers installed at */usr/local/include/mona/* after running above commands.


####ABC Installation

  - [ABC](https://vlab.cs.ucsb.edu/ABC/).

  ```
    $ cd <your home directory or a preferred directory>
    $ git clone --recursive git@github.com:vlab-cs-ucsb/ABC.git ABC // or use https://github.com/vlab-cs-ucsb/ABC.git
    $ cd ABC
    $ ./autogen.sh
    $ ./configure
    $ make all
    $ sudo make install
    $ sudo ldconfig
  ```

  If you want to use *ABC* with *JAVA* programs, make sure **JAVA_HOME** environment variable is set and has a valid Java installation path before running *./configure* command.


  At this point you should have all necessary libraries installed at *__/usr/local/lib__* directory. You should also have all necessary header files at
  *__/usr/local/include/glog__*,
  *__/usr/local/include/mona__*,
  *__/usr/local/include/abc__*
  directories.

Usage
============

####C++

  You can link to dynamic library generated in your program. An example executable for *__abc__* is generated for you and install in your system. You can run *__abc__* executable at your home directory as:

    $ abc -i  <input_file_path>
    $ abc --help #lists available command line options

  You can find example constraints at *__&lt;abc source folder&gt;/test/fixtures__*.

  You can take a look at *__&lt;abc source folder&gt;/src/main.cpp__* to see how *__abc__* is used in a C++ program as a shared library.

  (More documentation on ABC input language and format will be provided, please see *__&lt;abc-source-folder&gt;/test/fixtures__* folder for examples)

####JAVA

  You have to compile *__ABC__* with your *__JAVA_HOME__* path is set to a valid java path. Once you set your *__JAVA_HOME__* path, you need to install/re-install *__ABC__* on your system.

  You need to set Java VM argument __java.library.path__ to path where your shared libraries are install, or alternatively you can set __LD_LIBRARY_PATH__ environment variable to that path.

  You can use *__&lt;abc-source-folder&gt;/lib/ABCJava__* as an example Java program that calls __abc__.

  In your Java project all you have to do is to include the contents of *__&lt;abc-source-folder&gt;/lib/ABCJava/src/__*. *vlab.cs.ucsb.edu.DriverProxy.java* class is the class that makes abc calls.

ABC Language Specification
==========================

  ABC accepts input written in [SMT-LIB 2](http://smtlib.cs.uiowa.edu/language.shtml) format. ABC follows the syntax for the string theory that is defined by [CVC4](http://cvc4.cs.stanford.edu/wiki/Strings). Please see *__&lt;abc-source-folder&gt;/src/parser/lexer.lpp__* file for the list of operations ABC supports.

Contributing to ABC Source
==========================

####Workflow

  1- Always start working on your own branch, do not directly work on master branch

  2- Follow [rebase work flow whenever](https://www.atlassian.com/git/tutorials/merging-vs-rebasing) possible

  3- If you are not sure how to merge/rebase with/onto master, create a fresh branch out of master and first try to merge/rebase using that branch.

####Coding Style

  Please follow [Google C++ Style Guide](https://google.github.io/styleguide/cppguide.html).
