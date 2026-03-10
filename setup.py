from setuptools import setup, Extension

import os

print "FILE: " + __file__
cur_dir = os.path.dirname(os.path.abspath(__file__))
module_DriverProxy = Extension('PythonABCSolver',
                               sources=['src/PythonABCSolver.cpp'],
                               language='c++',
                               library_dirs=['/usr/local/lib', ],
                               libraries=['abc'],
                               include_dirs=['/usr/local/include',
                                             cur_dir,
                                             os.path.join(cur_dir, 'src'),
                                             ],
                               extra_compile_args=['-std=c++14'])


setup(name='PythonABCSolver',
      version='1.0.0.0',
      description='Python bindings for the ABC string solver',
      author="Lukas Dresel",
      author_email="lukas.dresel@cs.ucsb.edu",
      ext_modules=[module_DriverProxy])
