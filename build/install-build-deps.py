#!/usr/bin/env python

import shlex
import os
import platform
import subprocess
import sys
import re

ROOT_PATH = os.path.abspath(os.path.join(os.getcwd(), os.pardir) )
TMP_PATH = os.path.abspath(os.path.join(ROOT_PATH, 'tmp-installer-dir'))
ABC_PATH = ROOT_PATH

#TODO add package installation considering current os system
_packages_dev = (
  'g++',
  'git',
  'build-essential',
  'autoconf',
  'automake',
  'libtool',
  'intltool',
  'flex',
  'bison'
)

_project_dep = (
 {
     'name': 'glog',
     'url': 'https://github.com/google/glog.git',
     'checkout' : 'tags/v0.3.3',     
     'patch' : False,
     'path' : os.path.abspath(os.path.join(TMP_PATH, 'glog')),
     'autogen' : False,
     'autotools' : True
 },
 {
     'name': 'MONA',
     'url': 'https://github.com/cs-au-dk/MONA.git',
     'checkout' : '2f382f2111d54de594a5f6187f0a8449d4dd4b34',     
     'patch' : os.path.abspath(os.path.join(ABC_PATH, 'external', 'mona', 'mona_abc.patch')),
     'path' : os.path.abspath(os.path.join(TMP_PATH, 'MONA')),
     'autogen' : False,
     'autotools' : True
 },
 {
     'name': 'LibStranger',
     'url': 'https://github.com/vlab-cs-ucsb/LibStranger.git',
     'checkout' : False,     
     'patch' : False,
     'path' : os.path.abspath(os.path.join(TMP_PATH, 'LibStranger')),
     'autogen' : True,
     'autotools' : True
 }
)

def package_exists(pkg):
    return pkg in subprocess.check_output(['apt-cache', 'pkgnames']).splitlines()

def package_installed(pkg):
    out = subprocess.check_output(['apt-cache', 'policy', pkg]).splitlines()
    return not re.match(r"Installed: \(none\)", out[1].strip(), re.IGNORECASE)
    
def os_name():
    return os.name

def platform_system():
    return platform.system()

def runcmd(cmd, cwd=None, shell=False):
    print "{}\n".format(cmd)
    args = shlex.split(cmd)
    process = subprocess.Popen(args, cwd=cwd, shell=shell)
    process.communicate()
    retcode = process.poll()
    return retcode
    
def install(pkg):
    cmd = "sudo apt-get --assume-yes install {}".format(pkg)
    return runcmd(cmd)

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
    
def gitclone(url, local_path):
    cmd = "git clone {} {}".format(url, local_path)
    return runcmd(cmd)
    
def gitcheckout(target, cwd):
    cmd = "git checkout {} .".format(target)
    return runcmd(cmd, cwd)
    
def gitapply(patch, cwd):
    cmd = "git apply {}".format(patch)
    return runcmd(cmd,cwd)
    
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

def install_build_pkgs(pkglist):
    for pkg in pkglist:
        promt = "Checking for '{} ...".format(pkg)
        if package_exists:
            if not package_installed(pkg):
                print promt
                install(pkg)
                print " installed."
            else:
                print promt + " installed."
        else:
            print promt + " doesn't exists."
            
            
def install_dep_projets(prjlist):
    for prj in prjlist:
        print "Installing {}...".format(prj['name'])
        gitclone(prj['url'], prj['path'])
        if prj['checkout']: gitcheckout(prj['checkout'], prj['path'])
        if prj['patch']: gitapply(prj['patch'], prj['path'])
        if prj['autogen']: autogen(prj['path'])
        if prj['autotools']: autotools(prj['path'])
        
def build_abc():
    global ABC_PATH
    autogen(ABC_PATH)
    autotools(ABC_PATH)
            


def main(argv):
    
    if re.match(r".*linux.*", platform_system(), re.IGNORECASE):
        install_build_pkgs(_packages_dev)
    else:
        print "'{}' is not supported to install package dependencies.".format(platform_system())

    clean(TMP_PATH)
    mkdir(TMP_PATH)
    install_dep_projets(_project_dep)
    clean(TMP_PATH)
    build_abc();    
    print "build successfull."
    
if __name__ == "__main__":
   main(sys.argv[1:])



