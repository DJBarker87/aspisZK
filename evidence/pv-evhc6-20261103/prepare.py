"""Fresh plain-copy, namespace-complete coherent authority; no compiler."""
from pathlib import Path
import json,hashlib,lzma,shutil,struct,subprocess,time
B=Path(__file__).resolve().parent; R=B.parent; O=B/'objects'; S=B/'sources'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(n,v): (B/n).write_text(json.dumps(v,indent=2)+'\n')
def imports(p):
 b=p.read_bytes();assert b[:5]==b'olean';base,root=struct.unpack_from('<QQ',b,80)
 def u(o):return struct.unpack_from('<Q',b,o)[0]
 def name(p):
  if p&1:assert p==1;return ''
  o=p-base;tag=b[o+7];prefix=name(u(o+8));assert tag in [1,2]
  if tag==1:q=u(o+16)-base;t=b[q+32:b.index(0,q+32)].decode()
  else:t=str(u(o+16))
  return prefix+'.'+t if prefix else t
 arr=u(root-base+8)-base
 return list(dict.fromkeys(name(u(u(arr+24+8*i)-base+8)) for i in range(u(arr+8))))
assert not O.exists(),'fresh overlay required';O.mkdir();S.mkdir()
old=R/'codex-pv-evhc2-20261029';bridge=R/'codex-pv-bridge-20261101'
p=json.load(open(old/'plan.json'));cohort=[json.loads(l) for l in lzma.decompress((B/'NER_STREAM_B_COHORT.jsonl.xz').read_bytes()).splitlines()]
assert len(cohort)==16058;meta=json.load(open(B/'NER_STREAM_B_COHORT_META.json'))
assert hashlib.sha256(lzma.decompress((B/'NER_STREAM_B_COHORT.jsonl.xz').read_bytes())).hexdigest()==meta['cohort_sha256']
authority={v['module']:v for v in cohort};rp=json.load(open(B/'NER_REBUILT_OBJECT_PINS.json'))
for v in rp:assert authority[v['module']]['object_sha256']==v['sha256']
# Every coherent authority module is copied, so first-root namespace selection is complete.
copyrows=[]
for v in cohort:
 src=Path(v['object_path']);assert sha(src)==v['object_sha256'],str(src)
 dst=O/(v['module'].replace('.','/')+'.olean');dst.parent.mkdir(parents=True,exist_ok=True)
 for q in [dict(path=str(src),sha256=v['object_sha256'])]+v['companions']:
  f=Path(q['path']);assert sha(f)==q['sha256'],str(f)
  target=dst.with_suffix('.ir') if f.suffix=='.ir' else Path(str(dst)+str(f)[len(str(src)):])
  shutil.copyfile(f,target);assert not target.is_symlink() and target.stat().st_nlink==1
  assert sha(target)==q['sha256'];copyrows.append(dict(source=str(f),path=str(target),sha256=q['sha256']))
print('AUTHORITY COPIED',len(cohort),flush=True)
# Freeze ALL evhc3 privacy objects including previously reused event-only modules.
mods={m:dict(p['sources'].get(m,{})) for m in p['rebuild']+p['reuse']}
for m,s in mods.items():
 if not s:
  sp=Path(p['graph_source_pins'][m]['path']);s.update(path=str(sp),sha256=sha(sp),text=sp.read_text(),revision='evhc3 external source pin')
 assert hashlib.sha256(s['text'].encode()).hexdigest()==s['sha256'],m
 s['original_object']=p['events'][m]['path'];s['original_object_sha256']=p['events'][m]['sha256']
# Bridge exact active source comes from its successful receipt snapshot.
active=json.load(open(bridge/'ACTIVE-OBJECT-PINS.json'))
for k,h in active['files'].items():
 if not k.endswith('.olean'):continue
 obj=Path(k) if k.startswith('/') else bridge/k;m=obj.stem
 assert sha(obj)==h,m
 receipts=[]
 for f in bridge.glob('lean-*/receipt.json'):
  v=json.load(open(f))
  if v.get('module')==m and v['exit_status']==0:receipts.append((int(f.parent.name[5:]),f,v))
 _,f,v=max(receipts);src=v['sources'][0];sp=f.parent/'sources'/src;assert sha(sp)==v['source_hashes'][src]
 mods[m]=dict(path=str(sp),sha256=sha(sp),text=sp.read_text(),revision=v['source_revision'],original_object=str(obj),original_object_sha256=h,source_receipt=str(f))
assert len(mods)<=600,len(mods)
graph={m:imports(Path(s['original_object'])) for m,s in mods.items()}
order=[];seen=set()
def visit(m):
 if m in seen:return
 seen.add(m)
 if m in authority:return
 assert m in mods,('missing source',m)
 for d in graph[m]:visit(d)
 order.append(m)
for m in mods:visit(m)
consumer=bridge/'PV_BR_FixtureConsumer.lean';shutil.copyfile(consumer,S/consumer.name)
consumer_imports=[x for l in consumer.read_text().splitlines() if l.startswith('import ') for x in l[7:].split()]
for m in consumer_imports:assert m in authority or m in mods,m
for m,s in mods.items():
 dst=S/(m.replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);dst.write_text(s.pop('text'));assert sha(dst)==s['sha256']
for name in ['S2W_lean_host.py','S2W_run_host.py','lakefile.toml','lean-toolchain']:shutil.copyfile(old/name,B/name)
# All source fingerprints exist; no old private objects enter fresh overlay.
for m in mods:assert not (O/(m.replace('.','/')+'.olean')).exists(),m
sysroot='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
plan=dict(authority='NER_STREAM_B_COHORT.jsonl.xz',order=order,sources=mods,edges=graph,consumer_imports=consumer_imports,consumer_sha256=sha(consumer),LEAN_PATH=str(O)+':'+sysroot+'/lib/lean',sysroot=sysroot)
save('PLAN.json',plan);save('AUTHORITY-COPIES.json',copyrows)
# ID audit: global receipt/config names and sent ledger, no compiler.
used=[]
for job in R.glob('codex-*'):
 for pattern in ['lean-9139[0-6]','lean-91[4-9][0-9][0-9]','attempt-9139[0-6].json','attempt-91[4-9][0-9][0-9].json']:
  used.extend(str(f) for f in job.glob(pattern))
assert not used,used
save('PREFLIGHT.json',dict(status='PASS',authority_modules=len(cohort),rebuilds=len(order),old_overlay_objects_copied=0,ids_used=used,consumer_imports=consumer_imports,namespace_complete=True,plan_sha256=sha(B/'PLAN.json')))
print(json.dumps(dict(status='PASS',modules=len(cohort),rebuilds=len(order))),flush=True)
