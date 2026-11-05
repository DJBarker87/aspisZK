"""Reconcile raw ax2 roots, exact fixtures and full scanner without changing any forest."""
from pathlib import Path
import json,lzma,hashlib,collections,re,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];J=lambda p:json.loads(p.read_text());H=lambda b:hashlib.sha256(b).hexdigest();STD={'propext','Classical.choice','Quot.sound'}
receipts={p.parent.name:J(p)for p in E.glob('NHO_L*/receipt.json')};assert len(receipts)==40
for a,r in receipts.items():
 ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}and int(r['swaps'])==0
 if r['kind']=='lean':assert '-M7000'in r['command']
 if r['kind']=='link':assert '-O3'in r['command']
 assert r['exit_status']not in [124,137]
expected=J(E/'NHO_AUDIT_ROOTS.json')['roots'];results=[];binary=None;disagreements=[]
for i in range(29):
 a=f'NHO_L{i+11:03}';x=J(E/'NHO_audit'/('batch'+str(i))/('proof'+str(i)+'.json'))
 bp=J(E/a/'NHO_ProofDriver_BINARY_PIN.json');binary=binary or bp;assert binary==bp
 for r in x['results']:
  assert set(r['walked_axioms'])<=STD and set(r['collect_axioms'])<=STD
  if not r['equal']:
   assert r['root']=='NHC_DecodeModel.decoder_error'and not r['collect_axioms']and set(r['walked_axioms'])==STD
   disagreements.append(dict(root=r['root'],raw=r['walked_axioms'],summary=r['collect_axioms'],attempt=a,classification="C3-BIN(ab')(3): raw standard-only authoritative; exit1 retained",source='evidence/pool-leaves-20261105/NHC_AUDIT.json'))
  name='NHO_NEP_proof'+str(i)+'_'+r['root']+'_REACHABLE.txt';p=E/(name+'.xz');raw=lzma.decompress(p.read_bytes());assert H(raw)==(E/(name+'.sha256')).read_text().strip()
  results.append(dict(r,attempt=a,raw_graph=p.name,raw_graph_sha256=H(raw),archive_sha256=H(p.read_bytes())))
 assert x['exit_status']==receipts[a]['exit_status']==(1 if any(not r['equal']for r in x['results'])else 0)
assert len(results)==len(expected)==len({r['root']for r in results})and {r['root']for r in results}==set(expected)
fx=J(E/'NHO_audit/fixtures/fixtures.json');assert fx['exit_status']==0 and len(fx['results'])==8 and all(r['equal']for r in fx['results'])
wanted={'NEP_Planted.matcher':['NEP_Planted.matchAx'],'NEP_Planted.viaPrivate':['NEP_Planted.privateAx'],'NEP_Planted.proof':['NEP_Planted.proofAx'],'NEP_Planted.viaAux':['NEP_Planted.auxAx'],'NEP_MutateMatch.matcher':[],'NEP_MutatePrivate.viaPrivate':[],'NEP_MutateProof.proof':[],'NEP_MutateAux.viaAux':[]}
assert {r['root']:r['walked_axioms']for r in fx['results']}==wanted
assert J(E/'NHO_L009/NHO_ProofDriver_BINARY_PIN.json')==binary
walker=J(E/'NHO_WALKER_CONFORMANCE.json');assert walker['byte_identical']and H((E/'NHO_WALKER_SOURCE.lean.txt').read_bytes())==walker['sha256']==H((R/'evidence/axaudit2-20261102/NEP_WALKER.lean').read_bytes())
historical=J(R/'evidence/pool-retarget-20261105/NGK_L051/receipt.json');oldwalker=next(v['sha256']for p,v in historical['deps_fingerprint']['selected_objects'].items()if p.endswith('/NFA_WALKER.olean'))
walker_objects={}
for a,r in receipts.items():
 if r['kind']=='audit':
  p,v=next((p,v)for p,v in r['deps_fingerprint']['selected_objects'].items()if p.endswith('/NFA_WALKER.olean'));assert v['sha256']==oldwalker;walker_objects[p]=v
walker['compiled_object_pins']=walker_objects;walker['historical_conformance']='NGK_L051 identical compiled walker; canonical source freshly byte checked'
rows=[json.loads(l)for l in(E/'NHO_LOADED_scan.jsonl').read_text().splitlines()];bad=[r for r in rows if r['dangling']or r['duplicate_owners']or not r['imports_match']]
scan=dict(status='PASS'if not bad else'FAIL',exit_status=receipts['NHO_L010']['exit_status'],modules=len(rows),declarations=sum(r['declarations']for r in rows),edges=sum(r['edges']for r in rows),dangling=sum(len(r['dangling'])for r in rows),incompatible_owners=sum(len(r['duplicate_owners'])for r in rows),import_mismatches=sum(not r['imports_match']for r in rows),compatible_cached_replicas=sum(len(r['cached_replicas'])for r in rows),defects=bad,scan_sha256=H((E/'NHO_LOADED_scan.jsonl').read_bytes()),attempt='NHO_L010')
required=set(re.findall(r'^import ([\w.]+)',(E/'NHO_COMBINED_IMPORT.lean').read_text(),re.M));assert required<={r['module']for r in rows};scan['required_forests_loaded']=sorted(required)
(E/'NHO_SCAN.json').write_text(json.dumps(scan,indent=1)+'\n');conflicts=dict(status='NONE'if not bad else'FINDING',conflicts=[r for r in bad if r['duplicate_owners']],qualified_rows=[],reason='No conflict observed in complete selected canonical forest; no declaration/module patched or renamed',combined_import='NHO_L004',scan_attempt='NHO_L010')
(E/'NHO_CONFLICTS.json').write_text(json.dumps(conflicts,indent=1)+'\n')
audit=dict(status='PASS_RAW_STANDARD_WITH_AB_PRIME_DISAGREEMENT'if disagreements else'PASS',root_count=len(results),results=results,fixtures=fx['results'],same_proof_binary=binary,collect_axioms_disagreements=disagreements,raw_standard_only=True,walker_conformance=walker,headline='AspisR1.RPx_Deployed.deployed',combined_import='NHO_L004',scan='NHO_SCAN.json',no_new_theorem=True,cold_release_replay=False,failed_cache_attempts=['NHO_L001','NHO_L002','NHO_L003'])
(E/'NHO_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
metrics=dict(charged_slots=len(receipts),by_kind=dict(collections.Counter(r['kind']for r in receipts.values())),successful=sum(r['exit_status']==0 for r in receipts.values()),failures={a:r['exit_status']for a,r in receipts.items()if r['exit_status']},scope_wall_sum_seconds=sum(r['wall_seconds']for r in receipts.values()),peak_rss_kib=max(int(r['peak_rss_kib'])for r in receipts.values()),swaps=0,Kani=0,extraction=0,new_theorems=0,caps='MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64; Lean -M7000',timeouts=0,memory_kills=0)
(E/'NHO_METRICS.json').write_text(json.dumps(metrics,indent=1)+'\n')
print(json.dumps(dict(roots=len(results),disagreements=disagreements,scan={k:v for k,v in scan.items()if k not in ['defects','required_forests_loaded']},metrics=metrics)));assert not bad and scan['exit_status']==0
