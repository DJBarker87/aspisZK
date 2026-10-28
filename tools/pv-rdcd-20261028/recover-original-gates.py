"""Replay original structural scripts with deployed source reads, preserve expectations.
Only virtualized output paths change. SSH source reads become local read-only calls.
"""
from pathlib import Path
import json,subprocess,sys,hashlib,types,traceback,runpy
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028');O=D/'original-gates';O.mkdir(exist_ok=True)
bundle=json.loads((D/'structural-inputs.json').read_text());virtual={};reads=[];transforms=[]
readb,readt,writet=Path.read_bytes,Path.read_text,Path.write_text
run=subprocess.run
root='/pv-classify-virtual/'
def rb(p):
 s=str(p)
 if s.startswith(root):
  key=s[len(root):]
  if key in virtual:return virtual[key].encode()
  if '/stdlib/' in key:
   q=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')/key.split('/stdlib/')[1];b=readb(q)
  elif key=='evidence/pv-relink-20261028/block-buffer-sealed.rs.txt':b=readb(Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/block-buffer-0.10.4/src/sealed.rs'))
  elif key=='evidence/pv-fxmem-20261028/CORE-DEFAULT-SOURCE.rs.txt':b=readb(Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/default.rs'))
  elif key.startswith(('crates/','programs/')):b=readb(Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028/src')/key)
  elif key in bundle:b=bundle[key]['text'].encode()
  else:raise FileNotFoundError('Missing recorded gate input '+key)
  reads.append(dict(path=key,sha256=hashlib.sha256(b).hexdigest()));return b
 return readb(p)
def rt(p,*a,**kw):return rb(p).decode()
def wt(p,s,*a,**kw):
 key=str(p)
 if key.startswith(root):virtual[key[len(root):]]=s;return len(s)
 return writet(p,s,*a,**kw)
def sr(cmd,*args,**kw):
 if cmd[0]=='git':
  pins=json.loads(readt(D/'git-pins.json'));key=cmd[-1];return subprocess.CompletedProcess(cmd,0,pins[key]+'\n','')
 if cmd[0]=='ssh':
  old=repr(cmd)+kw.get('input','');new=[x.replace('nightly-2026-06-01','1.94.1').replace('zeroize-1.8.1','zeroize-1.9.0') for x in cmd[2:]]
  if kw.get('input'):kw['input']=kw['input'].replace('nightly-2026-06-01','1.94.1').replace('zeroize-1.8.1','zeroize-1.9.0')
  transforms.append(dict(original=old,deployed=repr(new)+kw.get('input','')))
  if len(new)==1:return run(new[0],shell=True,*args,**kw)
  return run(new,*args,**kw)
 return run(cmd,*args,**kw)
Path.read_bytes=rb;Path.read_text=rt;Path.write_text=wt;subprocess.run=sr
# Original relink helper validates each source against its provenance input.
# Repin only that provenance to the actual deployed files; preserve expected bodies.
prov='evidence/pv-cblib-20261027/std-provenance.json'
if prov in bundle:
 j=json.loads(bundle[prov]['text'])
 for k,v in j.items():
  q=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')/k
  if q.exists():v['sha256']=hashlib.sha256(readb(q)).hexdigest()
 virtual[prov]=json.dumps(j)
plans=[('V201',['pv-dlib-20261028/structural-encoder.py']),('V236',['pv-dlib-20261028/structural-update.py']),('V237',['pv-dlib-20261028/structural-default.py']),('V233',['pv-relink-20261028/bind-v233.py']),('V265',['pv-alib-20261027/structural-circle.py']),('V221,V222',['pv-fxmem-20261028/structural-zeroize.py'])]
res=[]
for ids,steps in plans:
 record=dict(rows=ids.split(','),steps=[],source_selection='1.94.1 sysroot; zeroize1.9.0; all other dependencies resolved versions unchanged; x86_64 Linux release')
 for step in steps:
  key='tools/'+step;code=bundle[key]['text'];entry=dict(path=key,original_sha256=bundle[key]['sha256']);record['steps'].append(entry)
  try:
   if '/bind-' in key:
    common=types.ModuleType('common');common.__file__=root+'tools/pv-relink-20261028/common.py';exec(compile(bundle['tools/pv-relink-20261028/common.py']['text'],common.__file__,'exec'),common.__dict__);sys.modules['common']=common
   exec(compile(code,root+key,'exec'),{'__file__':root+key,'__name__':'__main__'})
   entry.update(status='PASS',exit=0)
  except Exception as ex:
   entry.update(status='SOURCE GATE DISAGREEMENT' if isinstance(ex,(AssertionError,ValueError)) else 'INPUT/ASSOCIATION GAP',exit=1,error=str(ex),exception=type(ex).__name__,traceback=traceback.format_exc());break
 record['result']=record['steps'][-1]['status'];res.append(record)
 print(ids,record['result'],flush=True)
Path.read_bytes=readb;Path.read_text=readt;Path.write_text=writet;subprocess.run=run
(O/'results.json').write_text(json.dumps(dict(results=res,read_inputs=reads,command_source_substitutions=transforms,outputs=virtual),indent=2)+'\n')
