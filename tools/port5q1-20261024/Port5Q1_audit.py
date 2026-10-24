#!/usr/bin/env python3
"""Static receipt/source audit. No prover, binary rebuild or release replay."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]; E=R/'evidence/port5q1-20261024'; L=R/'docs/research/100bit-spend-path-20261013/lean'
BASE='54d782463e29eac4c9f83c9192124e6c3d1e1381'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*args): return subprocess.check_output(['git',*args],cwd=R,text=True).strip()
changed=set(filter(None,git('diff','--name-only',BASE).splitlines())) | set(filter(None,git('ls-files','--others','--exclude-standard').splitlines()))
allowed=('docs/research/100bit-spend-path-20261013/lean/Port5Q1_','tools/port5q1-20261024/','evidence/port5q1-20261024/')
assert all(p.startswith(allowed) for p in changed), sorted(p for p in changed if not p.startswith(allowed))
assert not any(Path(p).suffix in {'.olean','.ilean','.o','.elf','.so','.tar','.gz'} for p in changed)
receipts=[]
for p in sorted(E.glob('lean-*/receipt.json')):
 x=json.loads(p.read_text()); assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 for field in ['command','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']: assert field in x,(p,field)
 assert x['swaps']=='0'
 for src,digest in x['source_hashes'].items(): assert sha(p.parent/'sources'/src)==digest
 if x['exit_status']==0:
  for line in x['print_axioms']:
   m=re.search(r'\[([^]]*)\]',line)
   if m: assert set(t.strip() for t in m.group(1).split(',') if t.strip()) <= {'propext','Classical.choice','Quot.sound'},line
 receipts.append((p,x))
assert len(receipts)<=100
modules={}
for p in sorted(L.glob('Port5Q1_*.lean')):
 s=p.read_text(); stripped=re.sub(r'/\-.*?\-/','',s,flags=re.S); stripped=re.sub(r'--[^\n]*','',stripped)
 assert not re.search(r'\b(sorry|sorryAx|admit|axiom|native_decide|maxRecDepth|maxHeartbeats)\b',stripped),p
 names=re.findall(r'^theorem\s+(\w+)',stripped,re.M)
 for n in names: assert re.search(r'#print axioms\s+'+re.escape(n)+r'\b',stripped),(p,n)
 success=[(q,x) for q,x in receipts if x['exit_status']==0 and x['source_hashes'].get(p.name)==sha(p)]
 assert success,('No accepted receipt for final source',p)
 q,x=success[-1]
 assert len(x['print_axioms'])>=len(names),(p,names,x['print_axioms'])
 modules[p.stem]={'sha256':sha(p),'bytes':p.stat().st_size,'accepted_receipt':str(q.relative_to(R)),'theorems':names,'axioms':x['print_axioms']}
protected={}
for name in ['crates/aspis-r1-cost-probe/src/verifier.rs','crates/aspis-r1-cost-probe/src/fast_domain.rs','crates/aspis-core/src/field.rs','Cargo.lock']:
 p=R/name
 original=subprocess.check_output(['git','show',BASE+':'+name],cwd=R)
 assert hashlib.sha256(original).hexdigest()==sha(p),name
 protected[name]={'sha256':sha(p),'bytes':p.stat().st_size}
configs={p.stem for p in (R/'tools/port5q1-20261024').glob('lean-*.json')}
actual={x['attempt'] for _,x in receipts}; admission=sorted(configs-actual)
for a in admission: assert (E/(a+'-launcher.log')).is_file()
manifest={'schema':'focused-extractor-proof-packet-v1','job':'port5q1-20261024','branch':git('branch','--show-current'),'base_revision':BASE,'audit_revision':git('rev-parse','HEAD'),'formal_release_claim':False,'claim':'Conditional accepted query-row refinement to frozen2 saved-ten/twelve/completeState, on same Prepared/parsed data and actual source calls/flushes. See Complete.accepted and README trust boundaries.','budget':{'actual_lean':len(receipts),'lean_limit':100,'kani':0,'kani_limit':60,'pre_lean_admission_failures':admission},'modules':modules,'protected_sources':protected,'attempts':[{'receipt':str(p.relative_to(R)),**{k:x[k] for k in ['attempt','source_revision','source_hashes','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}} for p,x in receipts],'source_change_assessment':'New prefixed proof/tool/evidence only. No shipped/feature/wire/parameter changes. No ELF rebuild trigger; no runtime/adversarial/frozen-manifest replay. Cached inherited dependencies reused, not a release rebuild.','inherited_elf_pins':{'status':'historical evidence only; not freshly rebuilt','default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','Pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}}
(E/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'modules':len(modules),'theorems':sum(len(x['theorems']) for x in modules.values()),'actual_lean':len(receipts),'passing_attempts':sum(x['exit_status']==0 for _,x in receipts),'admission_failures':admission,'shipped_changes':False}))
