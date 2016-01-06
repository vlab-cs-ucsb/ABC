#!/usr/bin/env python

import shlex
import os
import platform
import subprocess
import sys
import re

ROOT_PATH = os.path.abspath(os.path.join(os.getcwd(), os.pardir) )
TMP_PATH = os.path.abspath(os.path.join(ROOT_PATH, 'tmp-installer-dir'))
LIB_PATH = os.path.abspath(os.path.join(ROOT_PATH, 'lib'))
ABC_PATH = ROOT_PATH

class OSystem:
    unknown = 0    
    linux = 1
    osx = 2

def os_name():
    return os.name

def platform_system():
    return platform.system()
    
def get_current_os():
    if re.match(r".*linux.*", platform_system(), re.IGNORECASE):
        return OSystem.linux
    elif re.match(r".*darwin.*", platform_system(), re.IGNORECASE):
        return OSystem.osx
    else:
        print("'{}' is not supported to install package dependencies.".format(platform_system()))
    return OSystem.unknown
    
CURRENT_OS = get_current_os()

#custom_env = os.environ.copy()
#if CURRENT_OS == OSystem.osx:
#    custom_env['CXXFLAGS'] = "-stdlib=libc++"
#    custom_env['CC'] = "clang"
#    custom_env['CXX'] = "clang++"


if (CURRENT_OS == OSystem.linux):
    _packages_dev = (
      'g++',
      'git',
      'build-essential',
      'autoconf',
      'automake',
      'autoheader'
      'libtool',
      'intltool',
      'flex',
      'bison'
    )
elif (CURRENT_OS == OSystem.osx):
    _packages_dev = (
     {
         'name'     : 'autoconf',
         'curl'     : 'http://ftpmirror.gnu.org/autoconf/autoconf-2.69.tar.gz',     
         'extract'  : True,
         'path'     : os.path.abspath(os.path.join(TMP_PATH, 'autoconf')),
         'autogen'  : False,
         'autotools': True,
         'install'  : True,
         'prefix'   : "/usr/local"
     },
     {
         'name'     : 'automake',
         'curl'     : 'http://ftpmirror.gnu.org/automake/automake-1.15.tar.gz',
         'extract'  : True,     
         'path'     : os.path.abspath(os.path.join(TMP_PATH, 'automake')),
         'autogen'  : False,
         'autotools': True,
         'install'  : True,
         'prefix'   : "/usr/local"
     },
     {
         'name'     : 'libtool',
         'curl'     : 'http://ftpmirror.gnu.org/libtool/libtool-2.4.6.tar.gz',
         'extract'  : True,
         'path'     : os.path.abspath(os.path.join(TMP_PATH, 'libtool')),
         'autogen'  : False,
         'autotools': True,
         'install'  : True,
         'prefix'   : "/usr/local"
     },
     {
         'name'     : 'bison',
         'curl'     : 'http://ftp.gnu.org/gnu/bison/bison-3.0.2.tar.gz',
         'extract'  : True,
         'path'     : os.path.abspath(os.path.join(TMP_PATH, 'libtool')),
         'autogen'  : False,
         'autotools': True,
         'install'  : True,
         'prefix'   : "/usr/local"
     }
    )

_glog_co = 'tags/v0.3.3'
if CURRENT_OS == OSystem.osx:
    _glog_co = 'tags/v0.3.4'
    
_project_dep = (
 {
     'name'     : 'glog',
     'url'      : 'https://github.com/google/glog.git',
     'checkout' : _glog_co,     
     'patch'    : False,
     'path'     : os.path.abspath(os.path.join(TMP_PATH, 'glog')),
     'autogen'  : False,
     'autotools': True,
     'install'  : True
 },
 {
     'name'     : 'MONA',
     'url'      : 'https://github.com/cs-au-dk/MONA.git',
     'checkout' : '2f382f2111d54de594a5f6187f0a8449d4dd4b34',     
     'patch'    : os.path.abspath(os.path.join(ABC_PATH, 'external', 'mona', 'mona_abc.patch')),
     'path'     : os.path.abspath(os.path.join(TMP_PATH, 'MONA')),
     'commands' : ['autoreconf -fvi'], 
     'autogen'  : False,
     'autotools': True,
     'install'  : True
 },
 {
     'name'     : 'LibStranger',
     'url'      : 'https://github.com/vlab-cs-ucsb/LibStranger.git',
     'checkout' : False,     
     'patch'    : False,
     'path'     : os.path.abspath(os.path.join(TMP_PATH, 'LibStranger')),
     'autogen'  : True,
     'autotools': True,
     'install'  : True
 },
 {
     'name'     : 'googlemock',
     'submodule': True,
     'url'      : False,
     'checkout' : False,
     'patch'    : False,
     'path'     : os.path.abspath(os.path.join(LIB_PATH, 'googletest', 'googlemock')),
     'commands' : ['autoreconf -fvi'],     
     'autogen'  : False,
     'autotools': True,
     'install'  : False
 }
)



def package_exists(pkg):
    return pkg in subprocess.check_output(['apt-cache', 'pkgnames']).splitlines()

def package_installed(pkg):
    try:
        out = subprocess.check_output(['apt-cache', 'policy', pkg])
    except subprocess.CalledProcessError:
        return False

    outString = out.decode(sys.getdefaultencoding()).strip()
    return not re.match(r".*Installed: \(none\).*", outString, re.IGNORECASE)
    
def is_xcode_installed():
    try:
        out = subprocess.check_output(['xcode-select', '--print-path'])
    except subprocess.CalledProcessError:
        return False

    outString = out.decode(sys.getdefaultencoding()).strip()
    return re.match(r".+", outString, re.IGNORECASE)
    
def is_project_installed(pkg):
    try:
        out = subprocess.check_output(['which', pkg])
    except subprocess.CalledProcessError:
        return False

    outString = out.decode(sys.getdefaultencoding()).strip()
    return re.match(r".*/usr/local/.*", outString, re.IGNORECASE)

def runcmd(cmd, cwd=None, shell=False):
    print("{}\n".format(cmd))
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
    cmd = "mkdir {}".format(name)
    return runcmd(cmd)
    
def clean(name):
    rmrdir(name)
    
def gitclone(url, local_path):
    cmd = "git clone {} {}".format(url, local_path)
    return runcmd(cmd)
    
def download(url, path):
    cmd = "curl -L -o {}.tar.gz {}".format(path, url)
    return runcmd(cmd)
    
def extract(path):
    mkdir(path)
    cmd = "tar -xzf {}.tar.gz --strip 1 -C {}".format(path, path)
    return runcmd(cmd)
    
def gitcheckout(target, cwd):
    cmd = "git checkout {} .".format(target)
    return runcmd(cmd, cwd)
    
def gitsubmoduleinit(cwd):
    cmd = 'git submodule init'
    runcmd(cmd, cwd)
    cmd = 'git submodule update'
    return runcmd(cmd, cwd)
    
def gitapply(patch, cwd):
    cmd = "git apply {}".format(patch)
    return runcmd(cmd,cwd)
    
def autogen(cwd):
    cmd = './autogen.sh'
    return runcmd(cmd, cwd)
    
def autotools(cwd, install=True, prefix=None):
    if prefix:
        cmd = "./configure --prefix={}".format(prefix)
    else:
        cmd = "./configure"

    runcmd(cmd, cwd=cwd)
    cmd = 'make all'
    runcmd(cmd,cwd)
    if (install):
        cmd = 'sudo make install'
        runcmd(cmd,cwd)
        if CURRENT_OS == OSystem.linux:
            cmd = 'sudo ldconfig'
            runcmd(cmd, cwd)
    return

def invoke(func, args):
    return func(*args)
    
def invoke_commands(commands, cwd):
    for cmd in commands:
        runcmd(cmd, cwd)
    return
    

def install_build_pkgs(pkglist):
    for pkg in pkglist:
        promt = "Checking for '{} ...".format(pkg)
        if package_exists(pkg):
            if not package_installed(pkg):
                print(promt)
                install(pkg)
                print(" installed.")
            else:
                print(promt + " installed.")
        else:
            print (promt + " doesn't exists.")
            
            
def install_dep_projects(prjlist):
    global ABC_PATH
    prefix = None
    for prj in prjlist:
        if is_project_installed(prj['name']):
            print("Skipping installation of '{}'".format(prj['name']))
        else:
            print("Installing {}...".format(prj['name']))
            if 'url'       in prj and prj['url']       : gitclone(prj['url'], prj['path'])
            if 'curl'      in prj and prj['curl']      : download(prj['curl'], prj['path'])
            if 'extract'   in prj and prj['extract']   : extract(prj['path'])    
            if 'checkout'  in prj and prj['checkout']  : gitcheckout(prj['checkout'], prj['path'])
            if 'submodule' in prj and prj['submodule'] : gitsubmoduleinit(ABC_PATH)        
            if 'patch'     in prj and prj['patch']     : gitapply(prj['patch'], prj['path'])
            if 'commands'  in prj and prj['commands']  : invoke_commands(prj['commands'], prj['path'])       
            if 'autogen'   in prj and prj['autogen']   : autogen(prj['path'])
            if 'prefix'    in prj and prj['prefix']    : prefix = prj['prefix']     
            if 'autotools' in prj and prj['autotools'] : autotools(prj['path'], prj['install'], prefix)
        
def build_abc():
    global ABC_PATH
    autogen(ABC_PATH)
    autotools(ABC_PATH)
            
def main(argv):
    global CURRENT_OS

    clean(TMP_PATH)
    mkdir(TMP_PATH)
    if CURRENT_OS == OSystem.linux:
        install_build_pkgs(_packages_dev)
    elif CURRENT_OS == OSystem.osx:
        if not is_xcode_installed():
            print("XCode is missing, please install it first!")
            return
        install_dep_projects(_packages_dev)
    else:
        print("'{}' is not supported to install package dependencies.".format(platform_system()))

    install_dep_projects(_project_dep)
    clean(TMP_PATH)
    build_abc();    
    print("build finished, check console for any errors.")
    
if __name__ == "__main__":
   main(sys.argv[1:])



