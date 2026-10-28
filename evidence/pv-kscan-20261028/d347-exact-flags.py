from pathlib import Path
import json,collections,hashlib,re,subprocess
E=Path(__file__).resolve().parent;C=Path('/private/tmp/pv-kscan-cache-20261028');R='/home/dombarker/project-offloads/codex-pv-kscan-20261028';W=R+'/d347/workspace';db=json.loads((C/'d347-source-db.json').read_text());ps=json.loads((E/'d347-input.json').read_text())['passes'];rs=json.loads((C/'d347-receipts.json').read_text());plans=json.loads((E/'d347-plans.json').read_text());bs=json.loads((E/'d347-source-bindings.json').read_text());payload={};num=47
for base in ['D024','D011','D012','D013','D014','D015','D016','D025','D018','D041']:
 groups={}
 for i in plans[base]['indices']:
  p=next(p for p in ps if p['index']==i);r=rs[p['receipt_blob']];m={k:v for k,v in r['source_sha256'].items() if k.endswith(('.rs','Cargo.toml','Cargo.lock'))};sig=hashlib.sha256(json.dumps(m,sort_keys=True).encode()).hexdigest();groups.setdefault(sig,dict(m=m,ps=[],r=r))['ps'].append(p)
 for g in groups.values():
  n=f'D{num:03}';num+=1;m=g['m'];subset=g['ps'];r=g['r'];rev=re.match('[0-9a-f]+',r['source_revision'])[0];original={k:h for k,h in m.items()};assert all(h in db for h in m.values()),n
  updates={W+'/'+k:db[h]['text'] for k,h in m.items()};files=[dict(path=W+'/'+k,sha256=h,origin=db[h]['origin'],kind=db[h]['kind']) for k,h in m.items()]
  if base=='D041':
   paths=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'Cargo.toml','crates','programs','tools','docs/research/v8-r0-zk-20261009/refine'],text=True).splitlines()
   for f in paths:
    if not f.endswith('Cargo.toml') or f in m:continue
    b=subprocess.check_output(['git','show',rev+':'+f]);updates[W+'/'+f]=b.decode();m[f]=hashlib.sha256(b).hexdigest();files.append(dict(path=W+'/'+f,sha256=m[f],origin=rev+':'+f,kind='original revision Cargo workspace manifest'))
  plan=dict(plans[base]);cmd=plan['command'];cmd=cmd[:cmd.index('-Z')] if '-Z' in cmd else cmd;cmd=[v for v in cmd if v!='--no-overflow-checks'];orig=subset[0]['command']
  if '--no-overflow-checks' in orig:cmd+=['--no-overflow-checks']
  for i,v in enumerate(orig):
   if v=='-Z':cmd+=['-Z',orig[i+1]]
  if '--no-assertion-reach-checks' in orig:cmd+=['--no-assertion-reach-checks']
  if base=='D041':cmd+=['--harness','pv_srcid']
  plan['command']=cmd;env={k:v for k,v in r.get('environment',{}).items() if k not in ['CARGO_TARGET_DIR'] and v is not None};env['RUSTFLAGS']=r.get('environment',{}).get('RUSTFLAGS') or '';env['CARGO_TARGET_DIR']=R+'/d347/cache';plan['env']=env;plan['indices']=[p['index'] for p in subset];plan['harnesses']=[p['harness'] for p in subset];upath=R+'/d347/'+n+'/updates.json';plan['updates_file']=upath;plan['source_checks']={W+'/'+k:h for k,h in m.items()};payload[upath]=json.dumps(updates);plans[n]=plan
  bs.append(dict(run=n,indices=plan['indices'],basis='Complete original receipt source maps AND original recorded RUSTFLAGS/profile environment; original compiler-affecting Kani switches restored. Earlier diagnostic inventories retained but superseded.',files=files));print(n,base,plan['indices'])
(E/'d347-plans.json').write_text(json.dumps(plans,indent=2)+'\n');(E/'d347-source-bindings.json').write_text(json.dumps(bs,indent=2)+'\n');(C/'d347-exact-payload.json').write_text(json.dumps(payload));(E/'d347-exact-runs.json').write_text(json.dumps([f'D{i:03}' for i in range(47,num)])+'\n')
