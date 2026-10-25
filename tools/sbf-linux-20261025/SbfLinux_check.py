"""Ordinary local pure/mock validation runner. Never invokes native backend."""
import hashlib
import io
import json
import pathlib
import resource
import sys
import time
import unittest
from unittest.mock import patch
from contextlib import ExitStack
import ctypes
import os

BASE = pathlib.Path(__file__).resolve().parents[2]
SOURCE = BASE/'tools/sbf-linux-20261025'
EVIDENCE = BASE/'evidence/sbf-linux-20261025'


def pin(path):
    raw=path.read_bytes()
    return dict(sha256=hashlib.sha256(raw).hexdigest(),size=len(raw))


def main():
    assert len(sys.argv)==3 and sys.argv[1] in ('v2','v3','v4','v5','final')
    assert len(sys.argv[2])==40 and all(c in '0123456789abcdef' for c in sys.argv[2])
    label,revision=sys.argv[1:]
    start=time.monotonic()
    import SbfLinux_tests
    out=io.StringIO()
    with ExitStack() as stack:
        for owner,names in ((ctypes,('CDLL','PyDLL')), (os,('fork','execve','chroot',
                'setuid','setgid','setresuid','setresgid','setgroups','unshare')),
                (resource,('setrlimit',))):
            for name in names:
                stack.enter_context(patch.object(owner,name,create=True,
                    side_effect=AssertionError('forbidden real effect '+name)))
        result=unittest.TextTestRunner(stream=out,verbosity=2).run(
            unittest.defaultTestLoader.loadTestsFromModule(SbfLinux_tests))
    wall=time.monotonic()-start
    usage=resource.getrusage(resource.RUSAGE_SELF)
    assert usage.ru_maxrss < 512*2**20, 'local RSS budget'
    package={str(p.relative_to(BASE)):pin(p) for p in sorted(SOURCE.glob('*.py'))}
    dependencies={}
    for module in list(sys.modules.values()):
        path=getattr(module,'__file__',None)
        if path and path.endswith('.py') and pathlib.Path(path).is_file():
            dependencies[path]=pin(pathlib.Path(path))
    log=EVIDENCE/('SbfLinux-tests-'+label+'.log')
    receipt=EVIDENCE/('SbfLinux-tests-'+label+'.json')
    assert not log.exists() and not receipt.exists(), 'preserve previous evidence'
    log.write_text(out.getvalue())
    data=dict(command=['PYTHONDONTWRITEBYTECODE=1',sys.executable,
                      'tools/sbf-linux-20261025/SbfLinux_check.py',label,revision],
              source_revision=revision,source_overlay=package,dependencies=dependencies,
              interpreter=dict(path=sys.executable,version=sys.version,**pin(pathlib.Path(sys.executable))),
              tests=result.testsRun,exit=0 if result.wasSuccessful() else 1,
              wall_seconds=wall,peak_rss_bytes=usage.ru_maxrss,swap=usage.ru_nswap,
              platform=sys.platform,axioms='N/A',log=pin(log),
              validation='pure/mock only; no Linux C calls/fork/exec/credential/limit changes',
              limits='local process below 512 MiB; no host job launched',
              native_runtime_closure='NOT established; loaded Python source hashes are local test provenance')
    receipt.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    print(out.getvalue())
    print(json.dumps({k:data[k] for k in ('tests','exit','wall_seconds','peak_rss_bytes','swap','axioms')}))
    return data['exit']

if __name__=='__main__':
    raise SystemExit(main())
