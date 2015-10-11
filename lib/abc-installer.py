#!/usr/bin/env python

import os
import shlex
from subprocess import Popen

ROOT_PATH = os.path.abspath(os.path.join(os.getcwd(), os.pardir) )
TMP_PATH = os.path.abspath(os.path.join(ROOT_PATH, 'tmp-installer-dir'))
GLOG_PATH = os.path.abspath(os.path.join(TMP_PATH, 'glog'))
MONA_PATH = os.path.abspath(os.path.join(TMP_PATH, 'MONA'))
LIBSTRANGER_PATH = os.path.abspath(os.path.join(TMP_PATH, 'LibStranger'))
ABC_PATH = ROOT_PATH


def runcmd(cmd, cwd=None, shell=False):
    print "{}\n".format(cmd)
    args = shlex.split(cmd)
    p = Popen(args, cwd=cwd, shell=shell)
    p.communicate()
    return

def rm(name):
    cmd = "rm {}".format(name)
    return runcmd(cmd)
    
def rmdir(name):
    cmd = "rmdir {}".format(name)
    return runcmd(cmd)

def rmrdir(name):
    cmd = "rm -rf {}".format(name)
    return runcmd(cmd)
    
def mv(src, dst):
    cmd = "mv {} {}".format(src, dst)
    return runcmd(cmd)

def cp(src, dst):
    cmd = "cp -r {} {}".format(src, dst)
    return runcmd(cmd)
    
def mkdir(name):
    cmd = "mkdir {} -p".format(name)
    return runcmd(cmd)
    
def clean(name):
    rmrdir(name)
    mkdir(name)
    
def gitclone(url, cwd):
    cmd = "git clone {} .".format(url)
    return runcmd(cmd, cwd)
    
def gitcheckout(target, cwd):
    cmd = "git checkout {} .".format(target)
    return runcmd(cmd, cwd)
    
def autogen(cwd):
    cmd = './autogen.sh'
    return runcmd(cmd, cwd)
    
def autotools(cwd):
    cmd = './configure'
    runcmd(cmd,cwd)
    cmd = 'make all'
    runcmd(cmd,cwd)
    cmd = 'sudo make install'
    runcmd(cmd,cwd)
    cmd = 'sudo ldconfig'    
    return runcmd(cmd, cwd)
    
def gitapply(patch, cwd):
    cmd = "git apply {}".format(patch)
    return runcmd(cmd,cwd)


clean(TMP_PATH)

print "-----------Installing Project Dependencies-----------------\n"

print "\n\n1 - Installing Glog logging library"
mkdir(GLOG_PATH)
gitclone('https://github.com/google/glog.git', GLOG_PATH)
gitcheckout('tags/v0.3.3', GLOG_PATH)
autotools(GLOG_PATH)

print "\n\n2 - Installing Mona automata library"
mkdir(MONA_PATH)
gitclone('https://github.com/cs-au-dk/MONA.git', MONA_PATH)
MONA_PATCH = os.path.abspath(os.path.join(ABC_PATH, 'external', 'mona', 'mona_abc.patch'))
gitapply(MONA_PATCH, MONA_PATH)
autotools(MONA_PATH)

print "\n\n3 - Installing Libstranger string analysis library"
mkdir(LIBSTRANGER_PATH)
gitclone('https://github.com/vlab-cs-ucsb/LibStranger.git', LIBSTRANGER_PATH)
runcmd("chmod u+x autogen.sh", LIBSTRANGER_PATH)
autogen(LIBSTRANGER_PATH)
autotools(LIBSTRANGER_PATH)

print "\n\n4 - Installing ABC constraint solver and model counter"
autogen(ABC_PATH)
autotools(ABC_PATH)

rmrdir(TMP_PATH)

print "\n...done."
