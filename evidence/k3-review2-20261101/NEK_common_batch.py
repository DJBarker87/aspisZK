"""Three independent capped scopes over ONE immutable cfg-selected source bundle."""
from NEK_common_contracts import *
from NEK_host import py,admit,launch,B
from concurrent.futures import ThreadPoolExecutor,as_completed
import threading,lzma,time

def prepare():
 c=read_json(ROOT/'evidence/slice-s-leaves-20261029/NEC_CLOSED.json')[0];items=[];base=None;index=39;clause_index=0;attrs=[]
 for rp in c['kani_receipt_paths']:
  o,p,m,req,clauses=make(rp)
  if base is None:base=dict(o);base_parent=p;base_native=m;requirements=req
  else:
   assert o[p]==base[p] and o[m]==base[m],('not identical body/input fixture',rp)
  for j,clause in enumerate(clauses):
   attrs.append('#[cfg_attr(all(kani,NEK_clause_'+str(clause_index)+'),kani::ensures(|r| ('+clause+') != cfg!(NEK_invert)))]\n')
   for neg in [False,True]:
    a=f'NEK_K{index:03}';index+=1
    items.append(dict(attempt=a,original_receipt=rp,clause=j,cfg='NEK_clause_'+str(clause_index),predicate=clause,negative=neg))
   clause_index+=1
 base[base_parent]=base[base_parent].replace('fn asq8_common(',requirements+''.join(attrs)+'fn asq8_common(',1)
 assert all('static mut' not in t for t in base.values())
 (E/'NEK_COMMON_IMMUTABLE.json.xz').write_bytes(lzma.compress(json.dumps(base,sort_keys=True).encode()))
 (E/'NEK_COMMON_BATCH_PLAN.json').write_text(json.dumps(items,indent=2)+'\n')
 diff=[]
 for n,t in base.items():
  old=frozen(n);diff.extend(__import__('difflib').unified_diff((old or b'').decode().splitlines(True),t.splitlines(True),fromfile='a/'+n if old else '/dev/null',tofile='b/'+n))
 (E/'NEK_COMMON_IMMUTABLE.patch').write_text(''.join(diff));return base,items

def upload(base):
 admit('NEK_COMMON_IMMUTABLE_INPUT')
 code=f'''from pathlib import Path
import json,zlib,base64,hashlib
b=Path({B!r});s=b/'NEK_src';f=json.loads((b/'NEK_FROZEN_RS.json').read_text())
for n in json.loads((b/'NEK_OVERLAY.json').read_text()):
 p=s/n
 if n in f:p.write_text(f[n])
 elif p.is_file():p.unlink()
o=json.loads(zlib.decompress(base64.b64decode({base64.b64encode(zlib.compress(json.dumps(base).encode())).decode()!r})))
for n,t in o.items():p=s/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
(b/'NEK_OVERLAY.json').write_text(json.dumps(list(o)))
for n,t in { {n:(E/n).read_text() for n in ['NEK_gate.py','NEK_graph.py']}!r}.items():(b/n).write_text(t)
pins={{str(q.relative_to(s)):hashlib.sha256(q.read_bytes()).hexdigest() for q in s.rglob('*') if q.is_file() and q.suffix in ['.rs','.toml','.lock']}}
(b/'NEK_SOURCE_PINS.json').write_text(json.dumps(pins));print(len(pins))
'''
 r=py(code);assert r.returncode==0,r.stderr

def cfg(item,base):
 a=item['attempt'];rp=item['original_receipt'];original=read_json(ROOT/rp);ni=(original.get('native_command') or original['command'])[:];manifest=ni[ni.index('--manifest-path')+1];oldsrc=manifest.split('/programs/')[0]
 ni=[v.replace(oldsrc,B+'/NEK_src') for v in ni];ni=[B+'/NEK_target' if i>0 and ni[i-1]=='--target-dir' else v for i,v in enumerate(ni)]
 if '--features' not in ni:ni+=['--features','pool-adapter,private-leaf-salts']
 env={k:v for k,v in original['env'].items() if k!='LEAN_PATH'};env.update(TMPDIR=B+'/NEK_tmp',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0')
 env['RUSTFLAGS']=env.get('RUSTFLAGS','')+' --cfg '+item['cfg']+(' --cfg NEK_invert' if item['negative'] else '')
 return dict(attempt=a,kind='kani',module='r1_pool_adapter::NDM_native::common_contract',sources=['NEK_src/'+n for n in base]+['NEK_gate.py','NEK_graph.py','NEK_src/Cargo.lock'],command=['python3','NEK_gate.py',a+'.json'],native_command=ni,env=env,timeout=original.get('timeout',180),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint=dict(original_receipt=rp,original_sha256=sha((ROOT/rp).read_bytes()),immutable_bundle_sha256=sha((E/'NEK_COMMON_IMMUTABLE.json.xz').read_bytes()),split_conjunct=item['clause'],selected_cfg=item['cfg']),copy_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',expected_time='optimized cached compile, one independent original postcondition conjunct, no native field multiplication',print_axioms='N/A: kani',concurrency_policy='at most three 8GiB scopes, immutable source/manifest/pins; independent cfg targets and disjoint evidence paths')

write_lock=threading.Lock()
def worker(item,base):
 a=item['attempt'];rc=launch(cfg(item,base))
 r=py(f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{p.name:p.read_text() for p in b.glob({(a+'-*check.json')!r})}}))
''');assert r.returncode==0,r.stderr
 for n,t in json.loads(r.stdout).items():(E/n).write_text(t)
 v=verdict((E/a/'stdout.log').read_text());result=dict(attempt=a,original_receipt=item['original_receipt'],verdict=v,expected='FAIL' if item['negative'] else 'PASS',negative=item['negative'],method='immutable cfg-selected local-index Box common conjunct contract',clause=item['clause'])
 with write_lock:
  with (E/'NEK_RESULTS.jsonl').open('a') as f:f.write(json.dumps(result)+'\n')
 print(a,v,flush=True)
 return result

def run():
 base,items=prepare()
 if os.environ.get('NEK_PLAN_ONLY'):print(len(items),'windows; immutable source preflight PASS');return
 # No previous native scope may still read this source tree during setup.
 upload(base)
 pending=[x for x in items if not (E/x['attempt']/'receipt.json').exists()]
 with ThreadPoolExecutor(max_workers=3) as pool:
  futures=[]
  for i,item in enumerate(pending):
   futures.append(pool.submit(worker,item,base))
   if i<2:time.sleep(2)
  for future in as_completed(futures):future.result()
if __name__=='__main__':run()
