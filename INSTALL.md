Setup
============
ABC is a C++ executable and a C++ shared library with JNI interfaces. You can 
use it as a static or dynamic lib or you can run it from command line.

### Download
  
```
$ cd <your home directory or a preferred directory>
$ git clone --recursive git@github.com:vlab-cs-ucsb/ABC.git ABC # or use https://github.com/vlab-cs-ucsb/ABC.git
```
ABC testing depends on [googletest and googlemock](https://github.com/google/googletest) as subprojects. It is important to clone with ``--recursive`` option.

### Easy(Automated) Setup
  - [ABC](https://vlab.cs.ucsb.edu/ABC/). Clone ABC source and run build script. It automatically tries to install required system packages and dependent projects; [Glog](https://github.com/google/glog) and [Mona](http://www.brics.dk/mona/). After installing dependencies, it installs ABC. If script does not work please try step-by-step guide or contact us. (That script is tested with Linux machines. You can still use build script in other posix systems if you resolve system dependencies manually.)
  
  ```
  $ cd ABC/build
  $ ./install-build-deps.py
  ```

### Step-by-Step(Semi-automated) Setup
#### System Dependencies
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

#### Project Dependencies
  - [Glog](https://github.com/google/glog) logging library for C++. It is an autotools project. 
  Please follow the instructions in their website if the below shortcut doesn't work for you.

  ```
  $ cd <your home directory or a preferred directory>
  $ git clone https://github.com/google/glog.git
  $ cd glog
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


#### ABC Installation

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
