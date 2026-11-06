"""Read-only receipt aggregation after the single final gate; no host launches."""
from pathlib import Path
import json,lzma,re,hashlib,subprocess
E=Path(__file__).resolve().parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
prelaunch=[json.loads(l) for l in (E/'NLJ_ATTEMPTS.jsonl').read_text().splitlines() if json.loads(l)['attempt']=='NLJ_L017']
assert len(prelaunch)==1 and prelaunch[0]['launched'] is False
receipts=[json.loads((E/f'NLJ_L{i:03}/receipt.json').read_text()) if i!=17 else prelaunch[0] for i in range(1,151)]
native=[json.loads((E/f'NLJ_K{i:03}/receipt.json').read_text())for i in range(1,41)]
positives=[3,5,7,9,11,13,15,17,19,21,24,26,30,32,34,36,38]
controls=[4,6,8,10,12,14,16,18,20,22,25,27,31,33,35,37,39]
assert all(native[i-1]['exit_status']==0 for i in positives)
assert all(native[i-1]['exit_status'] not in [0,124,137,143] for i in controls)
assert len(receipts)==150 and len(native)==40
assert H(E/'NLJ_KMX.patch')==H(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch')
assert (E/'NLJ_L113/receipt.json').exists()
assert json.loads((E/'NLJ_L113/receipt.json').read_text())['exit_status']==0
fixtures=json.loads((E/'NLJ_audit/fixtures/fixtures.json').read_text());assert fixtures['exit_status']==0 and len(fixtures['results'])==8 and all(r['equal'] for r in fixtures['results'])
scan=[json.loads(x)for x in(E/'NLJ_LOADED_scan.jsonl').read_text().splitlines()]
assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
allowed={'propext','Classical.choice','Quot.sound'}
all_results=[];groups=[];disagreements=[];unexpected=[]
for i in range(30):
 p=E/f'NLJ_audit/proof{i}/proof{i}.json';r=json.loads(p.read_text());groups.append(dict(target=f'proof{i}',exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],receipt_sha256=H(p),results=len(r['results'])))
 for v in r['results']:
  all_results.append(v)
  if not set(v['walked_axioms'])<=allowed:unexpected.append(v)
  if not v['equal']:disagreements.append(v)
 assert r['exit_status'] in [0,1]
manifest=json.loads((E/'NLJ_AUDIT_ROOTS.json').read_text())
assert sorted(v['root']for v in all_results)==sorted(manifest['roots'])
assert not unexpected
assert all(v['root']=='NHC_DecodeModel.decoder_error' and set(v['collect_axioms'])<=allowed for v in disagreements)
assert len(disagreements)<=1
pin=json.loads((E/'NLJ_PREDECESSOR_COMPARISON.json').read_text());assert all(not r['mismatches']for r in pin.values())
closure=json.loads(lzma.decompress((E/'NLJ_CLOSURE_PINS.json.xz').read_bytes()));export=json.loads((E/'NLJ_EXPORT.json').read_text())
combined=json.loads((E/'NLJ_L113/receipt.json').read_text())
axioms=combined['print_axioms'];assert len(axioms)==76 and not any('sorryAx'in x for x in axioms)
for line in axioms:
 if 'depends on axioms:'in line:
  names=set(re.findall(r'\[(.*)\]',line)[0].split(', '));assert names<=allowed,line
natives=[]
for i,r in enumerate(native,1):
 assert json.loads((E/f'NLJ_K{i:03}-lock-check.json').read_text())['unchanged']
 p=E/f'NLJ_K{i:03}-graph-check.json';g=json.loads(p.read_text());assert g['graph_matches_frozen']
 natives.append(dict(attempt=r['attempt'],exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],receipt_sha256=H(E/f'NLJ_K{i:03}/receipt.json'),graph_check_sha256=H(p)))
for r in receipts+native:
 if r.get('launched') is False:continue
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},r['attempt']
 admission=json.loads((E/(r['attempt']+'-admission.json')).read_text());assert admission['exit']==0 and admission['reservation']['allowed'] is True
 diskfiles=list(E.glob(r['attempt']+'-disk-*.json'));assert diskfiles and json.loads(diskfiles[-1].read_text())['free']>=40*1024**3
# Local source/patch pins; no source changes after final import are accepted.
selected=json.loads((E/'NLJ_MODULES.json').read_text())
for m,f in selected['selected_receipts'].items():
 tested=E/Path(f).parent/'sources/NLJ_generated'/(m+'.lean');assert H(tested)==H(E/'NLJ_generated'/(m+'.lean'))
fields=['attempt','kind','module','launched','reason','command','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms','limits']
metrics=[{k:r.get(k)for k in fields}for r in receipts+native]
# Keep full exact metrics as a compressed artifact; no dependency fingerprints are duplicated here.
raw=(json.dumps(metrics,indent=1)+'\n').encode();(E/'NLJ_METRICS.json.xz').write_bytes(lzma.compress(raw));(E/'NLJ_METRICS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
audit=dict(status='COMPLETED_WITH_RETAINED_COLLECTOR_DISAGREEMENT'if disagreements else'PASS_STANDARD_AXIOMS',target_established=False,headline='AspisR1.RPx_Deployed.deployed',combined_audits=1,combined_import=dict(attempt='NLJ_L113',exit_status=0,wall_seconds=combined['wall_seconds'],peak_rss_kib=combined['peak_rss_kib'],swaps=combined['swaps'],source_revision=combined['source_revision'],print_axioms=axioms),scope_limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,Lean_M=7000,scope_timeout_seconds=180),scan=dict(exit_status=0,modules=len(scan),dangling=0,duplicate_owners=0,import_mismatches=0,cached_replicas=sum(len(r.get('cached_replicas',[]))for r in scan)),raw_ax2=dict(required_roots=len(manifest['roots']),results=len(all_results),nonstandard_axioms=[],collector_disagreements=disagreements,groups=groups,raw_verdicts_retained=True),predecessors=pin,exports=export,budget_interpretation='Every NLJ_L slot is conservatively charged, including support/audit/link and unlaunched L017; no claim of150 successful Lean compilations',budget=dict(Kani=dict(used=40,ceiling=40),Lean_support=dict(used=150,ceiling=150,launched_scopes=149,charged_prelaunch_failures=['NLJ_L017']),extraction=dict(used=0,ceiling=0)),native=dict(local_final_positive_control_pairs=17,superseded_pilot=['NLJ_K001','NLJ_K002'],timeout_no_credit=['NLJ_K023','NLJ_K028','NLJ_K029'],independent_error_negative='NLJ_K040',physical_parent_cut_admitted=False,graph_validation_every_run=True,offline=True,lock_unchanged_every_run=True,kmx_patch_sha256=H(E/'NLJ_KMX.patch'),runs=natives),closed_rows=[],qualified_rows=[],source_body_equalities=dict(TX1_137='PROVED',TX1_087='OPEN',TX1_094='OPEN'),new_trust_rows=[],p6_d188='Retained option-A reclassification; not removed',metrics='NLJ_METRICS.json.xz',frozen_verifier_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',pool_revision='b936275465',pool_elf_sha256='e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc')
(E/'NLJ_AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n')
assert not [p for p in E.rglob('*')if p.is_file()and p.stat().st_size>20000000]
print(json.dumps(dict(status=audit['status'],charged_lean=150,charged_kani=40,roots=len(all_results),collector_disagreements=len(disagreements),row_promotions=0)))
