#!/usr/bin/env python3
"""Tiny in-memory archive-policy tests; no compiler or namespace invocation."""
import importlib.util,json,pathlib,sys,tarfile,time,resource,hashlib,subprocess
start=time.monotonic();p=pathlib.Path(__file__).with_name('SbfInputs_prepare.py');s=importlib.util.spec_from_file_location('prep',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
cases=[('crate-1/src/lib.rs',tarfile.REGTYPE,0o644,True),('crate-1/src/',tarfile.DIRTYPE,0o755,True),('/crate-1/x',tarfile.REGTYPE,0o644,False),('crate-1/../x',tarfile.REGTYPE,0o644,False),('other/x',tarfile.REGTYPE,0o644,False),('crate-1/x',tarfile.SYMTYPE,0o644,False),('crate-1/x',tarfile.LNKTYPE,0o644,False),('crate-1/x',tarfile.FIFOTYPE,0o644,False),('crate-1/x',tarfile.REGTYPE,0o4644,False),('crate-1/.cargo-ok',tarfile.REGTYPE,0o644,False),('crate-1/id_rsa',tarfile.REGTYPE,0o600,False),('crate-1/a//b',tarfile.REGTYPE,0o644,False)]
rows=[]
for name,kind,mode,expected in cases:
 t=tarfile.TarInfo(name);t.type=kind;t.mode=mode
 try:m.member_path(t,'crate-1');actual=True
 except AssertionError:actual=False
 assert actual==expected;rows.append(dict(name=name,expected=expected,actual=actual))
u=resource.getrusage(0)
r=dict(cases=rows,exit=0,command=[sys.executable,'-B',__file__],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),inputs={str(q):hashlib.sha256(q.read_bytes()).hexdigest() for q in [p,pathlib.Path(__file__)]},wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,swap=u.ru_nswap,print_axioms='N/A')
with pathlib.Path('evidence/sbf-inputs-20261024/synthetic-tests.json').open('x') as f:json.dump(r,f,indent=2);f.write('\n')
print('12 archive-policy cases passed')
