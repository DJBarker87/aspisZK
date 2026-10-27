#!/usr/bin/env python3
"""Read-only source/import/cache inventory; no compiler or scope."""
import hashlib,json,pathlib,re,subprocess,sys
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-runjoin8-20261026'
prefix='docs/research/v8-r0-zk-20261009/lean/'
rev='1d20aab293cdff52b8af138489cd8c0e8f1e1fe7'
r=subprocess.run(['ssh','-o','BatchMode=yes','dombarker@100.108.41.90','python3 -c '+__import__('shlex').quote("import json,pathlib; e=json.load(open('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json')); print(json.dumps([str(p.relative_to(r)) for s in e['LEAN_PATH'].split(':') for r in [pathlib.Path(s)] for p in r.rglob('*.olean')]))")],capture_output=True,text=True,check=True)
cached={p[:-6].replace('/','.') for p in json.loads(r.stdout)}
seen=set();order=[];unknown=[];sources={}
def visit(m):
 if m in seen:return
 seen.add(m)
 is_cached=m in cached
 rel=m.replace('.','/')+'.lean'
 candidates=[root/prefix/rel,root/'docs/research/v8-r0-sem-proof-20261008/lean'/rel, root/'docs/research/100bit-spend-path-20261013/evidence/lean-append-tree-20261013/final-sources'/rel]
 candidates.append(e/'pending-proof-sources'/(m.split('.')[-1]+'.lean.txt'))
 candidates+=list((e/'read-only').glob('*/'+rel+'.txt'))
 p=next((p for p in candidates if p.is_file()),None)
 if p is None:
  snap=e/'read-only/next-source'/(rel+'.txt');snap.parent.mkdir(parents=True,exist_ok=True)
  for path in [prefix+rel,'evidence/privacy-recount-20261026/recount2/dict/'+prefix+rel+'.txt']:
   r=subprocess.run(['git','show',rev+':'+path],capture_output=True)
   if r.returncode==0:snap.write_bytes(r.stdout);p=snap;break
 if p is None:
  if not is_cached:unknown.append(m)
  return
 sources[m]=str(p.relative_to(root))
 for d in re.findall(r'^import\s+(\S+)',p.read_text(),re.M):visit(d)
 if not is_cached:order.append({'module':m,'source':str(p.relative_to(root)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
for m in sys.argv[2:]:visit(m)
x=dict(targets=sys.argv[2:],cache_count=len(cached),missing=order,unknown=unknown,prohibited_retries=['R1Z.EventsR1P2','R1Z.SimCostOuterRetry6'])
(e/sys.argv[1]).write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x,indent=2))
