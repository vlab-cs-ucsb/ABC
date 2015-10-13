#!/bin/sh

libtoolize && aclocal && automake --gnu --add-missing && autoreconf -ivf

