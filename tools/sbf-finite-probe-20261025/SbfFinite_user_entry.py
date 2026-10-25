raise SystemExit('SbfFinite SOURCE ONLY: public entry unconditionally disabled before imports')
# Complete dormant fixed entry. Removing the unconditional denial requires a new
# reviewed source publication and separate authority. No activation is supplied.
import hashlib
import importlib.abc
import importlib.util
import os
import stat
import sys

SbfFinite_ROOT = '/opt/aspis/SbfFinite-20261025-v1'
SbfFinite_PINS = {'SbfFinite_fixed.py': {'size': 185861, 'sha256': '68aac9e8bcd2dd7e0bb7f540fc64f290fc656f3a023c196d983d1a0e98ec8fd4'}, 'SbfFinite_validate.py': {'size': 2345, 'sha256': 'c5b1ce0ff34564ee02fed0dc66b7ee24b368eb7c58a3030471d0da4f22c3947c'}, 'SbfFiniteLinux_capture.py': {'size': 8545, 'sha256': '985d96c3ca35d4c7fa7a142fe8a7f6720784d473d1cb31a96f4ef3838d827b86'}, 'SbfFiniteLinux_abi.py': {'size': 8188, 'sha256': 'd54b4a72a9463aadd447196c439749632685ec85aafc6252791a8b18c6d61e76'}, 'SbfFiniteLinux_backend.py': {'size': 249, 'sha256': 'a5f4e62cdb8700431315b8d2a2de9bf5d764542def1b6fd37c245e714e2b98a7'}, 'SbfFinite_backend_candidate.py': {'size': 21315, 'sha256': '4746c1140158c76c2b5351c1e59126ff2ddeeb9402088be65b1d925b0853018c'}, 'SbfFinite_continue.py': {'size': 7852, 'sha256': '9b7a1327ba670f2ce1f6c22f029d705c694d53266787de3c46546bea02ed4d11'}, 'SbfFinite_observe.py': {'size': 5829, 'sha256': 'd1853bb466b9982d7517273cee613f014704a5df1b947239400234e1638aaec1'}, 'SbfFinite_process.py': {'size': 5583, 'sha256': '08fce0f0422245ed865bc94037ef35a6e16367bb3485eab1057f6ec2cfe87167'}, 'SbfFinite_package.py': {'size': 7365, 'sha256': 'd948e90d16bda805541d8fc5f8d50438e85d83a445c5c59be21909e498cfcacf'}, 'SbfFiniteRss_adapter.py': {'size': 4639, 'sha256': '3e668325a4c514df318c4a03d838a8bcdebf9c80ff89583af9b5e4c9533f08a5'}, 'SbfFiniteRss_guard.py': {'size': 8647, 'sha256': '90953ce4ab221422a014db32923162e6bf4d83f75ca7e615296c3b838c7b7518'}, 'SbfFiniteRss_sources.py': {'size': 4999, 'sha256': '08aed1aa640662e62c155cdcf881a386be54ea38b918b71ad3161f0c4d8594f5'}, 'SbfFiniteRss_reviewed.json': {'size': 69294, 'sha256': 'ce3415ad130a35de66ee29820326fe385daa99ab593f063b95e5efe442d5acaf'}, 'SbfFinite_launcher_pin.py': {'size': 205, 'sha256': '17bfe71ce30a5763852ab4b817d1b5c2f148e9e70dd8cea06fad879432c63a57'}, 'SbfFinite_package_pins.py': {'size': 1989, 'sha256': '3874c30b06698efd42cab0bb57b2a22b9487ea8fe3c91e8a8523e93cacfc151a'}}
SbfFinite_MODULE = 'SbfFinite_continue'
SbfFinite_FUNCTION = 'user_producer'
SbfFinite_ENV = {'HOME':'/probe','LC_ALL':'C','PATH':'/usr/bin','TMPDIR':'/tmp'}

def SbfFinite_require(ok,reason):
    if not ok:raise RuntimeError(reason)

def SbfFinite_identity(s):
    return (s.st_dev,s.st_ino,s.st_mode,s.st_uid,s.st_gid,s.st_nlink,s.st_size,s.st_mtime_ns,s.st_ctime_ns)

def SbfFinite_read(name,pin):
    # Only exact literal file names from the source-pinned module catalog.
    SbfFinite_require(name in SbfFinite_PINS and '/' not in name,'fixed module name')
    flags=os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW|os.O_CLOEXEC
    fd=os.open('/',flags)
    try:
        for part in ['']+SbfFinite_ROOT[1:].split('/'):
            if part:
                new=os.open(part,flags,dir_fd=fd);os.close(fd);fd=new
            s=os.fstat(fd)
            SbfFinite_require(stat.S_ISDIR(s.st_mode) and s.st_uid==s.st_gid==0 and not s.st_mode&0o022,'sealed source ancestry')
        source=os.open(name,os.O_RDONLY|os.O_NOFOLLOW|os.O_CLOEXEC|os.O_NONBLOCK,dir_fd=fd)
        try:
            first=os.fstat(source)
            SbfFinite_require(stat.S_ISREG(first.st_mode) and first.st_uid==first.st_gid==0 and first.st_nlink==1 and
                              stat.S_IMODE(first.st_mode)==0o444 and first.st_size==pin['size']<=4*2**20,'sealed source rights/size')
            chunks=[];size=0
            while True:
                b=os.read(source,min(65536,pin['size']-size+1))
                if not b:break
                size+=len(b);SbfFinite_require(size<=pin['size'],'sealed source growth');chunks.append(b)
            raw=b''.join(chunks)
            SbfFinite_require(size==pin['size'] and hashlib.sha256(raw).hexdigest()==pin['sha256'],'sealed source hash')
            SbfFinite_require(SbfFinite_identity(first)==SbfFinite_identity(os.fstat(source))==
                              SbfFinite_identity(os.stat(name,dir_fd=fd,follow_symlinks=False)),'sealed source FD/entry drift')
            return raw
        finally:os.close(source)
    finally:os.close(fd)

class SbfFinite_loader(importlib.abc.MetaPathFinder,importlib.abc.Loader):
    def __init__(self,raw):self.raw=raw
    def find_spec(self,fullname,path=None,target=None):
        if not fullname.startswith('SbfFinite'):return None
        name=fullname+'.py'
        SbfFinite_require(name in self.raw,'unlisted finite module import')
        return importlib.util.spec_from_loader(fullname,self,origin=SbfFinite_ROOT+'/'+name)
    def create_module(self,spec):return None
    def exec_module(self,module):
        name=module.__name__+'.py'
        module.__file__=SbfFinite_ROOT+'/'+name
        exec(compile(self.raw[name],module.__file__,'exec'),module.__dict__)

def SbfFinite_main():
    SbfFinite_require(sys.argv==[SbfFinite_ROOT+'/'+'SbfFinite_user_entry.py'], 'fixed noargument entry argv')
    SbfFinite_require(dict(os.environ)==SbfFinite_ENV,'fixed entry environment')
    SbfFinite_require(not any(n.startswith('SbfFinite') for n in sys.modules),'preloaded finite modules')
    SbfFinite_require(0<len(SbfFinite_PINS)<=64 and sum(p['size'] for p in SbfFinite_PINS.values())<=8*2**20,'finite source catalog bound')
    raw={n:SbfFinite_read(n,p) for n,p in SbfFinite_PINS.items()}
    loader=SbfFinite_loader(raw);sys.meta_path.insert(0,loader)
    try:
        module=__import__(SbfFinite_MODULE)
        return getattr(module,SbfFinite_FUNCTION)()
    finally:
        sys.meta_path.remove(loader)

if __name__=='__main__':
    raise SystemExit(SbfFinite_main())
