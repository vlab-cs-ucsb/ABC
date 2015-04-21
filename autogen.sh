#!/bin/sh

libtoolize && aclocal && automake --gnu --add-missing && autoconf

cp autogen.sh.glog external/glog/autogen.sh
cp autogen.sh.googletest external/googletest/autogen.sh 

