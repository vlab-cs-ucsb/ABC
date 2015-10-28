ABC
========
The Automata Based Counter ([ABC](https://vlab.cs.ucsb.edu/ABC/)) is a **string constriant** solver and **model counter**. ABC provides solutions to systems of string constraints in the form of a deterministic finite automaton. In addition ABC produces symbolic representation of the number of strings within a length bound, k, that satisfy a set of constraints. ABC can also output the number of satisfying solutions for a specific provided bound.

This document serves as a short introductory guide for ABC. Please see the publications for details of ABC algorithms. 

Publications
============
 - CAV'15
 - ...
 - Muath's
 - Fang's
 - Const.'s

LANGUAGE SPECIFICATION
============

###ABSTRACT GRAMMAR
  - [ABC](https://vlab.cs.ucsb.edu/ABC/). Clone ABC source and run build script. It automatically tries to install required system packages and dependent projects; [Glog](https://github.com/google/glog), [Mona](http://www.brics.dk/mona/), and [LibStranger](https://github.com/vlab-cs-ucsb/LibStranger). After installing dependencies, it installs ABC. If script does not work please try step-by-step guide or contact us. (That script is tested with Linux machines. You can still use build script in other posix systems if you resolve system dependencies manually.)
  
  ```
  $ cd <your home directory or a preferred directory>
  $ git clone --recursive ssh://git@phab-isstac.isis.vanderbilt.edu/diffusion/ABC/abc.git ABC
  $ cd ABC/build
  $ ./install-build-deps.py
  ```

###LANGUAGE SYNTAX
ABC supports (partially) SMTLIB-V2 language specification. We do provide our own operation names, once the SMT community finalizes its string theory language specifications, we will have support for it. ABC also supports an easy input language for pure Linear Arithmetic Constraints. 

####Examples

###CONCRETE OPERATIONS

  ```
  abbd
  adfk
  ```

####System Dependencies
  - C++ compiler with C++11 support. ABC compilation is tested with g++ 4.8.4 on Ubuntu 14.04.
  - [Git](https://git-scm.com/)

    ``$ sudo apt-get install git``
  - ABC is an autotools project, you need to setup autotools in your system. Please make sure you have installed all the tools below.

    ``$ sudo apt-get install build-essential autoconf automake libtool intltool ``
  - Lex and Yacc. ABC is tested with [Flex 2.5.35](https://www.gnu.org/software/flex/flex.html) and [Bison 3.0.2](https://www.gnu.org/software/bison/).

    ``$ sudo apt-get install flex bison``
  - Python (optional). A short installation script is written in pyhton.
    
    ``$ sudo apt-get install python``

####Project Dependencies
  - [Glog](https://github.com/google/glog) logging library for C++. It is an autotools project. Please follow the instructions in their website if the below shortcut doesn't work for you. (The latest version of the glog may not compile because of this [issue](https://github.com/google/glog/issues/52). Below commands checkouts a working version for Ubuntu 14.04 that is known to be working)

  ```
  $ cd <your home directory or a preferred directory>
  $ git clone https://github.com/google/glog.git
  $ cd glog
  $ git checkout tags/v0.3.3
  $ ./configure
  $ make all
  $ sudo make install
  $ sudo ldconfig
```
  You should have glog libraries installed at */usr/local/lib* and headers installed at */usr/local/include/glog/* after running above commands. 

  - [Mona](http://www.brics.dk/mona/) is used for symbolic representation of automata. 

  ```sh
    $ cd <your home directory or a preferred directory>
    $ git clone https://github.com/cs-au-dk/MONA.git
    $ cd MONA
    $ git apply <ABC_ROOT_DIR>/external/mona/mona_abc.patch     # Please see below paragraph for details
    $ ./configure
    $ make all
    $ sudo make install
    $ sudo ldconfig

  ```
  **(!)** Third command above cannot be executed without downloading ABC sources. You can run the mona installation after you downloaded ABC. The patch requires small modifications in three files. Those changes are necessary for ABC to compile and run. You can download ABC by following the commands in the corresponding section and come back here again. Instead of running that command you can manually modify the following files:

  1- *__MONA/DFA/makebasic.c__* as follows:
  ```c
  // DFA/makebasic.c
  #define MAX_EXCEPTION 50   /* LINE 27: change this to 4096. */
  #define MAX_VARIABLES 10   /* LINE 28: change this to 30    */
```
  You can set above declarations to larger values whenever you need and reinstall mona. (In case you get an *invariant violation error* message in makefile.c by MONA)

  2- *__MONA/BDD/bdd_external.h__* as follows:
  ```c
  \#ifndef __BDD_EXTERNAL_H
  \#define __BDD_EXTERNAL_H  /* LINE 22                       */

  \#ifdef __cplusplus
  \#define export _export   /* Put those 3 lines here         */
  \#endif
  
  \#include "bdd.h"          /* LINE 24                       */
  ```
  
  3- *__MONA/BDD/makefile.am__* as follows:
  ```c
  mona_HEADERS = bdd.h       /* LINE 9  change this line to: mona_HEADERS = bdd.h bdd_external.h bdd_dump.h  */
  ```
  
  If you choose to modify files manually, please go back and complete MONA compilation and installation. 
  
  You should have mona libraries installed at */usr/local/lib* and headers installed at */usr/local/include/mona/* after running above commands. 

  - [LibStranger](https://github.com/vlab-cs-ucsb/LibStranger) is an Automata-Based Symbolic String Analysis Library.
  
  ```
  $ cd <your home directory or a preferred directory>
  $ git clone https://github.com/vlab-cs-ucsb/LibStranger.git
  $ cd LibStranger
  $ ./autogen.sh
  $ ./configure
  $ make all
  $ sudo make install
  $ sudo ldconfig
  ```
  
  You should have LibStranger libraries installed at */usr/local/lib* and headers installed at */usr/local/include/stranger/* after running above commands.
  
####ABC Installation

  - [ABC](https://vlab.cs.ucsb.edu/ABC/).

  ```
    $ cd <your home directory or a preferred directory>
    $ git clone --recursive ssh://git@phab-isstac.isis.vanderbilt.edu/diffusion/ABC/abc.git ABC
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
  *__/usr/local/include/stranger__*,  
  *__/usr/local/include/abc__*  
  directories.

Usage
============

####C++

  You can link to dynamic library generated in your program. An example executable for *__abc__* is generated for you and install in your system. You can run *__abc__* executable at your home directory as:
  `` $ abc -f <input constraint file> ``
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

to be prepared...
