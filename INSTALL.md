# Setup

[ABC](https://vlab.cs.ucsb.edu/ABC/) is a C++ executable and a C++ shared library with JNI interfaces. You can 
use it as a static or dynamic library or you can run it from the command line.

### Download
  
```
$ cd <your home directory or a preferred directory>
$ git clone --recursive git@github.com:vlab-cs-ucsb/ABC.git ABC # or use https://github.com/vlab-cs-ucsb/ABC.git
```
ABC testing depends on [`googletest` and `googlemock`](https://github.com/google/googletest) as subprojects. It is important to clone with ``--recursive`` option.

### Easy (Automated) Setup
Clone the ABC repository and run the build script. It automatically tries to install required system packages and dependencies, namely [Glog](https://github.com/google/glog) and [Mona](http://www.brics.dk/mona/). After installing dependencies, it installs ABC. 

*This script has been tested on Linux. You can still use it on other POSIX systems if you resolve system packages and dependencies manually. If the script does not work, please try the step-by-step setup below or contact us.*
  
```
$ cd ABC/build
$ ./install-build-deps.py
```

### Step-by-Step (Semi-automated) Setup
#### System Dependencies
  - C++ compiler with C++14 support. Latest ABC compilation is tested with g++ 9.3.0 on Ubuntu 20.04.
  - [Git](https://git-scm.com/)

  ```
    $ sudo apt install git
  ```
  - ABC is an autotools project, you need to setup autotools in your system. Please make sure you have installed all the tools below.

  ```
    $ sudo apt install build-essential autoconf automake libtool intltool cmake
  ```
  - Lex and Yacc. ABC is tested with [Flex 2.6.0](https://www.gnu.org/software/flex/flex.html) and [Bison 3.0.4](https://www.gnu.org/software/bison/).

  ```
    $ sudo apt install flex bison
  ```

  - Python (optional). A short installation script is written in python.
    
  ```
    $ sudo apt install python
  ```

#### Project Dependencies
  - [Glog](https://github.com/google/glog), a logging library for C++. 
  
  *While it supports a variety of build systems, ABC has only been built with `cmake` as shown below. 
  If the commands below don't work for you, please follow the build instructions on [Glog's GitHub](https://github.com/google/glog).*

  ```
  $ cd <your home directory or a preferred directory>
  $ git clone https://github.com/google/glog.git
  $ cd glog
  $ cmake -S . -B build -G "Unix Makefiles"
  $ cmake --build build
  $ sudo cmake --build build --target install
  
  ```
  You should have Glog libraries installed at `/usr/local/lib` and headers installed at `/usr/local/include/glog/` after running the commands above. 

  - [Mona](http://www.brics.dk/mona/) is used for symbolic representation of automata. Don't forget to apply patch as shown below: 

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
  You should have Mona libraries installed at `/usr/local/lib` and headers installed at `/usr/local/include/mona/` after running the commands above. 


#### ABC Installation
*If you want to use ABC with Java programs, make sure the `JAVA_HOME` environment variable is set and has a valid Java installation path before running `./configure`.*

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

At this point you should have all necessary libraries installed at `/usr/local/lib` directory. You should also have all necessary header files at  
- `/usr/local/include/glog`,  
- `/usr/local/include/mona`,  
- `/usr/local/include/abc`  
