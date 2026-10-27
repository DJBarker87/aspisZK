#!/usr/bin/env python3
"""Compile-free final consistency check; never launches a proof/build."""
import hashlib,json,pathlib,re,subprocess
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-runjoin8-20261026';base='3478e00a58'
rs=[json.loads(p.read_text()) for p in e.glob('receipt-*.json')]
assert len(rs)==100 and sum(r['accepted'] for r in rs)==78
assert all(r['swaps']==0 for r in rs)
for r in rs:
 assert r['source_sha256']==hashlib.sha256((e/r['source_snapshot']).read_bytes()).hexdigest()
 if r['accepted']:
  for ax in r['axioms']:
   if 'does not depend on any axioms' in ax: continue
   groups=re.findall(r'\[([^]]*)\]',ax);assert len(groups)==1,ax
   assert set(groups[0].replace('\n','').replace(' ','').split(',')) <= {'propext','Classical.choice','Quot.sound'},ax

paths=subprocess.check_output(['git','diff','--name-only',base],cwd=root,text=True).splitlines()
paths+=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=root,text=True).splitlines()
paths=sorted(set(paths));active=[]
for n in paths:
 assert n.startswith(('evidence/pv-runjoin8-20261026/','tools/pv-runjoin8-20261026/','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_')) or n in ['crates/aspis-statement/src/pool_v1/pair_trace.rs','crates/aspis-statement/src/pool_v1/pair_trace_pv_runjoin8_roots.rs'],n
 p=root/n
 if p.is_file() and n.endswith('.lean'):
  h=hashlib.sha256(p.read_bytes()).hexdigest();matches=[r['attempt'] for r in rs if r['accepted'] and r['source_sha256']==h];assert matches,n
  s=p.read_text();code=re.sub(r'/\-[\s\S]*?\-/|--[^\n]*','',s)
  assert not re.search(r'\b(?:sorry|admit|native_decide|implemented_by)\b|^\s*axiom\s+',code,re.M)
  ts=set(re.findall(r'^theorem\s+(\w+)',s,re.M));prints=set(re.findall(r'^#print axioms\s+([\w.]+)',s,re.M));assert ts<=prints,(n,ts-prints)
  active.append(dict(path=n,sha256=h,accepted_receipts=matches))
for name in ['TrustItems','TrustEndpoint','TrustLedger']:
 n='docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_'+name+'.lean';assert subprocess.check_output(['git','show',base+':'+n],cwd=root)==(root/n).read_bytes()
p='crates/aspis-statement/src/pool_v1/pair_trace.rs';old=subprocess.check_output(['git','show',base+':'+p],cwd=root).decode();new=(root/p).read_text()
stanza='\n#[cfg(kani)]\n#[path = "pair_trace_pv_runjoin8_roots.rs"]\nmod pv_runjoin8_roots;\n'
assert new.count(stanza)==1
assert new.replace(stanza,'')==old
x=dict(kind='compile-free final source/receipt audit',base_revision=base,checked_through_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),lean_attempts=100,accepted=78,failed=22,kani_runs=8,active_accepted_modules=active,unchanged_records=['TrustItems','TrustEndpoint','TrustLedger'],production_body_unchanged=True,production_body_sha256=hashlib.sha256(old.encode()).hexdigest(),harness_sha256=hashlib.sha256((root/'crates/aspis-statement/src/pool_v1/pair_trace_pv_runjoin8_roots.rs').read_bytes()).hexdigest(),counts=dict(runtime_boundary=[2,2],fields=[8,8],native_residuals=[6,6],T_fields=[3,3]),fixtures=dict(transfer='OPEN',withdrawal='OPEN'),target_established=False)
(e/'final-source-audit.json').write_text(json.dumps(x,indent=2)+'\n');print('All 100 receipts and '+str(len(active))+' active accepted modules match; T/P records and production body unchanged.')
