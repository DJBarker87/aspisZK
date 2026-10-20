#!/usr/bin/env python3
"""Avoid Aeneas's name-pattern printer assertion on monomorphized names."""
import json,pathlib,subprocess,os
R=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref6-20261021')
E=R/'nullifier-monomorphic';dest=E/'generated-no-pattern-printer'
dest.mkdir(exist_ok=False)
reserved=0
for p in pathlib.Path('/sys/fs/cgroup').rglob('memory.max'):
    try:
        v=p.read_text().strip()
        if v!='max' and (p.parent/'cgroup.procs').read_text().strip():reserved+=int(v)
    except OSError:pass
assert reserved+8*2**30<=55*2**30
env=os.environ.copy();env.update(ASPIS_SOURCE_REV='0b0e77f5f',RUSTFLAGS='-C link-arg=-Wl,--threads=4')
cmd=['/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/bin/aeneas','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisBuilderNullifierSource','-dest',str(dest),'-loops-to-rec',str(E/'admission-renamed.llbc')]
rc=subprocess.run(['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(R/'capped.py'),str(E/'aeneas-no-pattern-printer'),'Monomorphic nullifier translation without diagnostic name-pattern printer; no compilation','--','timeout','180',*cmd],cwd=R/'source',env=env).returncode
print('aeneas exit',rc,flush=True)
