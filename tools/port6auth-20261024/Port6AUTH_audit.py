#!/usr/bin/env python3
"""Check the final focused packet; never launches a build or rewrites sources."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/port6auth-20261024'
L=R/'docs/research/100bit-spend-path-20261013/lean';BASE='6394df23891e699f4db152110f727b7cac678184'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=R,text=True).strip()
receipts=[(p,json.loads(p.read_text())) for p in sorted(E.glob('lean-*/receipt.json'))]
assert len(receipts)<=100
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
ledger=[]
for p,x in receipts:
 assert x['limits']==limits,(p,x['limits'])
 assert x['swaps']=='0',(p,x['swaps'])
 assert len(x['sources'])==1
 assert '-j1' in x['command'] and '-M4400' in x['command']
 for src,h in x['source_hashes'].items():assert sha(p.parent/'sources'/src)==h
 ledger.append({'receipt':str(p.relative_to(R)),'receipt_sha256':sha(p),**{k:x[k] for k in ['attempt','source_revision','command','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms','limits']}})
for p in E.glob('lean-*-reservation.json'):
 x=json.loads(p.read_text());assert x['reserved_bytes']+x['additional_bytes']<=x['limit_bytes']==55*1024**3
modules={};definitions=[]
for p in sorted(L.glob('Port6AUTH_*.lean')):
 s=p.read_text();assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',s),p
 assert not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats)',s),p
 matches=[(rp,x) for rp,x in receipts if x['exit_status']==0 and x['source_hashes'].get(p.name)==sha(p)]
 assert matches,('no green final source receipt',p)
 rp,x=matches[-1]
 expected=['AspisR1.'+p.stem+'.'+t for t in re.findall(r'^theorem (\w+)',s,re.M)]
 for th in expected:
  rows=[a for a in x['print_axioms'] if a.startswith("'"+th+"'")];assert len(rows)==1,(p,th,rows)
  assert set(re.findall(r'\b(?:propext|Classical.choice|Quot.sound|sorryAx)\b',rows[0])) <= {'propext','Classical.choice','Quot.sound'}
  assert '#print axioms '+th.rsplit('.',1)[1] in s
 definitions+=expected
 modules[p.stem]={'source_sha256':sha(p),'source_bytes':p.stat().st_size,'accepted_receipt':str(rp.relative_to(R)),'theorems':expected}
final=modules['Port6AUTH_Audit'];ar=json.loads((R/final['accepted_receipt']).read_text())
assert len(ar['print_axioms'])==len(definitions)
assert all('sorryAx' not in a for a in ar['print_axioms'])
changed=git('diff','--name-only',BASE).splitlines()
allowed=('docs/research/100bit-spend-path-20261013/lean/Port6AUTH_','tools/port6auth-20261024/','evidence/port6auth-20261024/')
assert all(p.startswith(allowed) for p in changed),changed
assert not git('diff',BASE,'--','crates','programs')
deps={}
for _,x in receipts:
 for obj,d in x['deps_fingerprint'].get('selected_objects',{}).items():
  module=Path(obj).name.removesuffix('.olean');src=L/(module+'.lean')
  if src.is_file():deps[module]={'source_sha256':sha(src),'source_path':str(src.relative_to(R)),'base_source_unchanged':not bool(git('diff',BASE,'--',str(src.relative_to(R))))}
for p in E.rglob('*.json'):
 assert p.stat().st_size<=5_000_000,('large derived JSON must be hash+size only',p)
manifest={'schema':'focused-source-authentication-proof-packet-v1','base_revision':BASE,'audit_generation_revision':git('rev-parse','HEAD'),'modules':modules,'actual_lean_attempts':len(receipts),'kani_runs':0,'preflight_failures':['lean-003: missing dependency object; Lean never entered'],'results':ledger,'dependency_sources':deps,'reused_evidence_assessment':'Pinned cached Lean objects and inherited closure evidence only; selected object hashes are recorded per attempt. Existing proof source is unchanged from research base. Not a coherent frozen-manifest rebuild or a new ELF identity gate.','status':'Concrete native-to-indexed-recovery-to-Q1 consumer and sufficient source-law transport proved; full driver CleanAcceptedModel, source trace/count/runtime instantiations remain open.'}
(E/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'modules':len(modules),'theorems':len(definitions),'actual_lean_attempts':len(receipts),'final_audit':final['accepted_receipt'],'peak_rss_kib':ar['peak_rss_kib'],'swaps':ar['swaps'],'protected_source_unchanged':True},indent=2))
