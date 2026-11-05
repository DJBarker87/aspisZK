"""Preserve the failed full gate and separately summarize independent diagnostics."""
from pathlib import Path
import json,lzma,hashlib,collections,re
E=Path(__file__).resolve().parent;R=E.parents[1];J=lambda p:json.loads(p.read_text());H=lambda b:hashlib.sha256(b).hexdigest();STD={'propext','Classical.choice','Quot.sound'}
receipts={p.parent.name:J(p)for p in E.glob('NII_L*/receipt.json')};assert len(receipts)==40
for a,r in receipts.items():
 ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}and int(r['swaps'])==0 and r['exit_status']not in [124,137]
 if r['kind']=='lean':assert '-M7000'in r['command']
 if r['kind']=='link':assert '-O3'in r['command']
 own=[s for s in ad['reservation'].get('populated_scopes',[])if any('S2W_run_host.py NII_'in c for c in s.get('processes',[]))];assert not own,(a,'overlapping own scope')
expected=J(E/'NII_AUDIT_ROOTS.json')['roots'];environments=J(E/'NII_AUDIT_MODULES.json');results=[];binary=None;disagreements=[]
for i in range(30):
 a=f'NII_L{i+10:03}';x=J(E/'NII_audit'/('batch'+str(i))/('proof'+str(i)+'.json'));pin=J(E/a/'NII_ProofDriver_BINARY_PIN.json');binary=binary or pin;assert pin==binary
 for r in x['results']:
  assert set(r['walked_axioms'])<=STD and set(r['collect_axioms'])<=STD
  if not r['equal']:disagreements.append(dict(root=r['root'],raw=r['walked_axioms'],summary=r['collect_axioms'],attempt=a,classification="(ab')(3): raw standard-only authoritative; actual audit exit retained"))
  name='NII_NEP_proof'+str(i)+'_'+r['root']+'_REACHABLE.txt';p=E/(name+'.xz');raw=lzma.decompress(p.read_bytes());assert H(raw)==(E/(name+'.sha256')).read_text().strip()
  results.append(dict(r,attempt=a,environment=environments[i],raw_graph=p.name,raw_graph_sha256=H(raw),archive_sha256=H(p.read_bytes())))
 assert x['exit_status']==receipts[a]['exit_status']==(1 if any(not r['equal']for r in x['results'])else 0)
assert len(results)==len(expected)==len({r['root']for r in results})and {r['root']for r in results}==set(expected)
fx=J(E/'NII_audit/fixtures/fixtures.json');assert fx['exit_status']==0 and len(fx['results'])==8 and all(r['equal']for r in fx['results'])
wanted={'NEP_Planted.matcher':['NEP_Planted.matchAx'],'NEP_Planted.viaPrivate':['NEP_Planted.privateAx'],'NEP_Planted.proof':['NEP_Planted.proofAx'],'NEP_Planted.viaAux':['NEP_Planted.auxAx'],'NEP_MutateMatch.matcher':[],'NEP_MutatePrivate.viaPrivate':[],'NEP_MutateProof.proof':[],'NEP_MutateAux.viaAux':[]}
assert {r['root']:r['walked_axioms']for r in fx['results']}==wanted and J(E/'NII_L008/NII_ProofDriver_BINARY_PIN.json')==binary
walker=J(E/'NII_WALKER_CONFORMANCE.json');assert walker['byte_identical']and H((E/'NII_WALKER_SOURCE.lean.txt').read_bytes())==walker['sha256']==H((R/'evidence/axaudit2-20261102/NEP_WALKER.lean').read_bytes())
historical=J(R/'evidence/pool-retarget-20261105/NGK_L051/receipt.json');oldwalker=next(v['sha256']for p,v in historical['deps_fingerprint']['selected_objects'].items()if p.endswith('/NFA_WALKER.olean'));objects={}
for a,r in receipts.items():
 if r['kind']=='audit':
  p,v=next((p,v)for p,v in r['deps_fingerprint']['selected_objects'].items()if p.endswith('/NFA_WALKER.olean'));assert v['sha256']==oldwalker;objects[p]=v
walker['compiled_object_pins']=objects
rows=[json.loads(l)for l in(E/'NII_LOADED_scan.jsonl').read_text().splitlines()];bad=[r for r in rows if r['dangling']or r['duplicate_owners']or not r['imports_match']];assert not bad and receipts['NII_L009']['exit_status']==0
partial=dict(status='PASS_PARTIAL_ONLY',exit_status=0,attempt='NII_L009',environment='NII_DIAGNOSTIC_IMPORT',modules=len(rows),declarations=sum(r['declarations']for r in rows),edges=sum(r['edges']for r in rows),dangling=sum(len(r['dangling'])for r in rows),incompatible_owners=sum(len(r['duplicate_owners'])for r in rows),import_mismatches=sum(not r['imports_match']for r in rows),compatible_cached_replicas=sum(len(r['cached_replicas'])for r in rows),defects=bad,scan_sha256=H((E/'NII_LOADED_scan.jsonl').read_bytes()))
required=set(re.findall(r'^import ([\w.]+)',(E/'NII_DIAGNOSTIC_IMPORT.lean').read_text(),re.M));assert required<={r['module']for r in rows};partial['required_partial_forests_loaded']=sorted(required)
scan=dict(status='FULL_GATE_BLOCKED_OWNER_CONFLICT',full_gate_pass=False,exit_status=None,reason='Requested full import NII_L001 failed; no full-environment scanner launch is possible and no exit0 is invented',conflict='NII_CONFLICTS.json',diagnostic=partial)
(E/'NII_SCAN.json').write_text(json.dumps(scan,indent=1)+'\n')
audit=dict(status='FULL_COMPOSITION_FAILED_OWNER_CONFLICT',full_composition_pass=False,full_composition_attempt='NII_L001',full_composition_exit_status=1,minimal_owner_pair_attempt='NII_L002',conflict='NII_CONFLICTS.json',diagnostic_root_count=len(results),diagnostic_raw_standard_only=True,diagnostic_only=True,results=results,fixtures=fx['results'],same_proof_binary=binary,collect_axioms_disagreements=disagreements,walker_conformance=walker,headline='AspisR1.RPx_Deployed.deployed',diagnostic_import_attempt='NII_L003',isolated_NHJ_attempt='NII_L039',scan='NII_SCAN.json',no_new_theorem=True,cold_release_replay=False)
(E/'NII_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
metrics=dict(charged_slots=len(receipts),by_kind=dict(collections.Counter(r['kind']for r in receipts.values())),successful=sum(r['exit_status']==0 for r in receipts.values()),failures={a:r['exit_status']for a,r in receipts.items()if r['exit_status']},scope_wall_sum_seconds=sum(r['wall_seconds']for r in receipts.values()),peak_rss_kib=max(int(r['peak_rss_kib'])for r in receipts.values()),swaps=0,Kani=0,extraction=0,new_theorems=0,caps='MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64; Lean -M7000',timeouts=0,memory_kills=0)
(E/'NII_METRICS.json').write_text(json.dumps(metrics,indent=1)+'\n')
# Fresh exact kernel statements with their complete axiom lines.
source=(E/'NII_PLAN_STATEMENTS.lean').read_text();log=(E/'NII_L040/stdout.log').read_text();quotes=[];lines=['# Exact kernel-loaded plan and headline statements','','Partial diagnostic environment (NII_DIAGNOSTIC_IMPORT); full all-slices owner conflict remains. These statements supply none of their physical/native hypotheses.','']
for name in re.findall(r'^#check @([\w.]+)',source,re.M):
 m=re.search(r'^@?'+re.escape(name)+r'(?:\.\{[^}]*\})? :',log,re.M);assert m,name
 ax=re.search("'"+re.escape(name)+"' (?:depends on axioms:\\s*\\[[^\\]]*\\]|does not depend on any axioms)",log[m.start():]);assert ax,name
 quote=log[m.start():m.start()+ax.end()];quotes.append(dict(name=name,attempt='NII_L040',quote_sha256=H(quote.encode()),axiom_line=ax[0]));lines+=['## '+name,'','```lean',quote,'```','']
assert len(quotes)==10 and receipts['NII_L040']['exit_status']==0
(E/'NII_STATEMENTS.md').write_text('\n'.join(lines)+'\n');(E/'NII_STATEMENT_QUOTES.json').write_text(json.dumps(quotes,indent=1)+'\n')
print(json.dumps(dict(diagnostic_roots=len(results),disagreements=disagreements,partial_scan={k:v for k,v in partial.items()if k not in ['defects','required_partial_forests_loaded']},metrics=metrics)))
